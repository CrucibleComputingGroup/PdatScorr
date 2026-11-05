"""Proof-only coherent abstraction of two identical total combinational cones.

Full input tuples gate shared symbolic results; unequal tuples permit unrelated
results. Cone identity and definedness are checked before the abstraction.
"""
from __future__ import annotations
import copy
import hashlib
import json
from pathlib import Path

from odc.temporal import checked_yosys, digest, yosys_path

COMBINATIONAL = {"$add", "$sub", "$mul", "$and", "$or", "$xor", "$xnor", "$not", "$logic_not",
    "$logic_and", "$logic_or", "$eq", "$ne", "$ge", "$gt", "$le", "$lt", "$reduce_and",
    "$reduce_or", "$reduce_xor", "$reduce_xnor", "$reduce_bool", "$mux", "$pmux", "$bmux",
    "$bwmux", "$shl", "$shr", "$sshl", "$sshr", "$shift", "$shiftx", "$neg", "$pos"}


def signature(module, prefix):
    inputs = {role: module["netnames"][prefix + role]["bits"] for role in ("ctl_i", "rs1_i", "rs2_i")}
    output = module["netnames"][prefix + "result"]["bits"]
    leaves = {}
    for role, bits in inputs.items():
        for i, bit in enumerate(bits):
            token = (role, i)
            if bit in leaves and leaves[bit] != token:
                raise ValueError("Aliased cone inputs need an explicit interface relation")
            leaves[bit] = token
    driver = {}
    for name, cell in module["cells"].items():
        for port, direction in cell["port_directions"].items():
            if direction == "output":
                for i, bit in enumerate(cell["connections"][port]):
                    if not isinstance(bit, int):
                        continue
                    if bit in driver:
                        raise ValueError("Multiple cone drivers")
                    driver[bit] = (name, cell, port, i)
    cache, cells, busy = {}, set(), set()
    def hashed(value):
        return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()
    def bit_term(bit):
        if bit in leaves:
            return hashed(["input", *leaves[bit]])
        if isinstance(bit, str):
            if bit not in ("0", "1", "x", "z"):
                raise ValueError("Unsupported constant")
            return hashed(["constant", bit])
        if bit in cache:
            return cache[bit]
        if bit not in driver:
            raise ValueError("Cone has an undeclared external input")
        name, cell, port, index = driver[bit]
        if cell["type"] not in COMBINATIONAL:
            raise ValueError("Cone is not a supported deterministic combinational function")
        if name in busy:
            raise ValueError("Combinational cycle")
        busy.add(name)
        children = {p: [bit_term(b) for b in bits] for p, bits in cell["connections"].items()
                    if cell["port_directions"][p] == "input"}
        key = hashed([cell["type"], cell["parameters"], children])
        busy.remove(name)
        cells.add(name)
        for p, direction in cell["port_directions"].items():
            if direction == "output":
                for i, b in enumerate(cell["connections"][p]):
                    cache[b] = hashed([key, p, i])
        return cache[bit]
    hashes = [bit_term(b) for b in output]
    return {"input_bits": inputs, "output_bits": output, "output_signature": hashes,
            "cone_cells": sorted(cells), "signature_sha256": hashed(hashes)}


def abstract_alu(design, top, directory: Path, *, yosys):
    mod = design["modules"][top]
    a = signature(mod, "reference.u_alu.u_alu.")
    b = signature(mod, "candidate.u_alu.u_alu.")
    if ({role: len(bits) for role, bits in a["input_bits"].items()}
            != {role: len(bits) for role, bits in b["input_bits"].items()}
            or len(a["output_bits"]) != len(b["output_bits"])):
        raise ValueError("Coherent cones require identical per-role input and output widths")
    if a["output_signature"] != b["output_signature"]:
        raise ValueError("ALU combinational cones differ under complete input renaming")
    if set(a["output_bits"]) & set(b["output_bits"]):
        raise ValueError("Overlapping cone outputs require a separate alias rule")
    # A matching structural signature is not sufficient for x/pmux defaults:
    # prove every output defined for every fully defined input tuple.
    cone = {"modules": {"AluCone": {"attributes": {"top": "1"},
        "ports": {**{r: {"direction": "input", "bits": bits} for r, bits in a["input_bits"].items()},
                  "result": {"direction": "output", "bits": a["output_bits"]}},
        "netnames": {**{r: {"hide_name": 0, "attributes": {}, "bits": bits} for r, bits in a["input_bits"].items()},
                     "result": {"hide_name": 0, "attributes": {}, "bits": a["output_bits"]}},
        "cells": {n: copy.deepcopy(mod["cells"][n]) for n in a["cone_cells"]}}}}
    cone_path = directory / "alu_cone.json"
    cone_path.write_text(json.dumps(cone) + "\n")
    proof = checked_yosys(yosys, f"read_json {yosys_path(cone_path)}\nhierarchy -check -top AluCone\n"
        "check -assert\nbwmuxmap\nbmuxmap\n"
        "sat -enable_undef -set-def-inputs -set-any-undef result -show result\n",
        directory, "alu_definedness", 60)
    log = Path(proof["log"]).read_text()
    if log.count("SAT solving finished - no model found.") != 1:
        raise ValueError("ALU output can be undefined, or definedness proof failed")
    nextbit = max(bit for cell in mod["cells"].values() for bs in cell["connections"].values()
                  for bit in bs if isinstance(bit, int)) + 1
    width = len(a["output_bits"])
    same = [nextbit]
    arbitrary_a = list(range(nextbit + 1, nextbit + 1 + width))
    arbitrary_b = list(range(nextbit + 1 + width, nextbit + 1 + 2 * width))
    chosen_b = list(range(nextbit + 1 + 2 * width, nextbit + 1 + 3 * width))
    prefix = "$pscorr_coherent_alu_"
    if any(n.startswith(prefix) for n in mod["cells"]):
        raise ValueError("ALU abstraction already applied")
    # Cut only consumers. The original function drivers remain unmodified and
    # become unused; optimization may subsequently remove their dead cones.
    alias = {**dict(zip(a["output_bits"], arbitrary_a)), **dict(zip(b["output_bits"], chosen_b))}
    for cell in mod["cells"].values():
        for port, direction in cell["port_directions"].items():
            if direction == "input":
                cell["connections"][port] = [alias.get(bit, bit) for bit in cell["connections"][port]]
    for port in mod["ports"].values():
        if port["direction"] == "output":
            port["bits"] = [alias.get(bit, bit) for bit in port["bits"]]
    def add(name, kind, con, params, dirs):
        mod["cells"][prefix + name] = {"hide_name": 1, "type": kind, "parameters": params,
            "attributes": {"pscorr_proof_only": 1}, "port_directions": dirs, "connections": con}
    full_a = [bit for bits in a["input_bits"].values() for bit in bits]
    full_b = [bit for bits in b["input_bits"].values() for bit in bits]
    add("inputs_equal", "$eq", {"A": full_a, "B": full_b, "Y": same},
        {"A_SIGNED": 0, "B_SIGNED": 0, "A_WIDTH": len(full_a), "B_WIDTH": len(full_b), "Y_WIDTH": 1},
        {"A": "input", "B": "input", "Y": "output"})
    for name, bits in (("a", arbitrary_a), ("b", arbitrary_b)):
        add(name, "$anyseq", {"Y": bits}, {"WIDTH": width}, {"Y": "output"})
    add("conditional_coherence", "$mux", {"A": arbitrary_b, "B": arbitrary_a, "S": same, "Y": chosen_b},
        {"WIDTH": width}, {"A": "input", "B": "input", "S": "input", "Y": "output"})
    return {"reference_cone": a, "candidate_cone": b, "definedness": proof,
            "cone_json_sha256": digest(cone_path), "full_input_tuple_bits": len(full_a),
            "coherence": "Equal COMPLETE input tuples imply equal symbolic results; unequal tuples permit independent results",
            "assumptions_added": 0, "hardware_modified": False,
            "domain": "Proof-only overapproximation, retaining every concrete paired RTL execution"}
