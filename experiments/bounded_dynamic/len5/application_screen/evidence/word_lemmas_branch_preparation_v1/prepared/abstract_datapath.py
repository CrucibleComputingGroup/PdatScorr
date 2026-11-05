#!/usr/bin/env python3
"""Proof-only LEN5 datapath overapproximation; NEVER a hardware optimization.

Each selected single combinational driver becomes an independent $anyseq value
each cycle. All original traces remain representable by choosing the original
driver values. A safety proof is therefore stronger; a counterexample may be
spurious. No state, tag, instruction, clock, reset or handshake driver is cut.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import re


BASE = "u_backend.u_exec_stage."
TARGETS = {
    "alu_result": {
        "alias": BASE + "u_alu_unit.u_alu.result_o", "width": 64,
        "source_suffix": "/exec-units/alu.sv:",
        "meaning": "ALU result payload; native request/result validity, tags and latency remain unchanged",
    },
    "mul_result": {
        "alias": BASE + "gen_mult_unit.u_mult_unit.gen_parallel_mult_unit.u_mult.result_o", "width": 64,
        "source_suffix": "/exec-units/mult.sv:",
        "meaning": "Multiplier result payload after original operation selection; native pipeline/control state retained",
    },
    "branch_taken": {
        "alias": BASE + "u_branch_unit.res_taken", "width": 1,
        "source_suffix": "/exec-units/branch_unit.sv:",
        "meaning": "Optional semantic branch outcome; original branch valid/tag/latency and downstream recovery logic retained",
    },
}
MODES = {"alu_mul": ("alu_result", "mul_result"),
         "alu_mul_branch_taken": ("alu_result", "mul_result", "branch_taken")}
PREFIX = "$pscorr_proof_only_datapath_"
# These exact pinned targets are currently $pmux. Allow an ordinary mux after
# harmless normalization, but never an arbitrary cell guessed from its width.
ALLOWED_DRIVERS = {"$mux", "$pmux", "$bmux", "$bwmux"}


def canonical_hash(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def _state_cell(cell):
    typ = cell["type"].lower()
    return "ff" in typ or "latch" in typ or typ.startswith("$mem") or typ in {"$sr", "$_sr_"}


def abstract_datapath(design: dict, top: str, mode: str = "alu_mul") -> tuple[dict, dict]:
    """Return an overapproximated proof model and an exact structural audit.

    The caller must establish upstream/source provenance and retain this audit.
    No new physical ports are added. All original aliases still refer to the
    same bits; only each whole, unique combinational Y driver is replaced.
    """
    if mode not in MODES:
        raise ValueError(f"Unknown proof abstraction mode: {mode}")
    if set(design.get("modules", {})) != {top}:
        raise ValueError("Expected exactly one flattened module")
    original = design["modules"][top]
    if any(name.startswith(PREFIX) for name in original["cells"]):
        raise ValueError("Refuse to abstract an already abstracted model")
    drivers = {}
    state_bits = set()
    inputs = set()
    for name, port in original["ports"].items():
        if port["direction"] == "inout":
            raise ValueError(f"Bidirectional port unsupported: {name}")
        if port["direction"] == "input":
            inputs.update(port["bits"])
    for name, cell in original["cells"].items():
        if not cell["type"].startswith("$"):
            raise ValueError(f"Unflattened/opaque cell: {name}")
        for port, bits in cell["connections"].items():
            direction = cell["port_directions"][port]
            if direction == "inout":
                raise ValueError(f"Bidirectional cell port unsupported: {name}.{port}")
            if direction == "output":
                for bit in bits:
                    if isinstance(bit, int):
                        drivers.setdefault(bit, []).append((name, port))
                if _state_cell(cell):
                    state_bits.update(bits)

    # Reject aliasing with explicit scalar/vector protocol/control ports.
    # Packed data structs are not cut by name: exact whole-Y equality below
    # ensures the selected result does not silently include their tag fields.
    protected = {}
    protocol = re.compile(r"(?:^|\.)(?:clk(?:_[io])?|rst_ni|reset(?:_[io])?|flush_i|"
                          r"\w*ready_[io]|\w*valid_[io]|\w*rob_idx_[io]|\w*tag_[io]|"
                          r"instr_rdata_i|issue_instr_i|issue_eu_ctl_i)$")
    for name, net in original.get("netnames", {}).items():
        if protocol.search(name):
            for bit in net["bits"]:
                if isinstance(bit, int):
                    protected.setdefault(bit, []).append(name)

    selected, selected_cells, selected_bits = [], set(), set()
    for target_name in MODES[mode]:
        spec = TARGETS[target_name]
        net = original["netnames"].get(spec["alias"])
        if net is None:
            raise ValueError(f"Missing audited payload alias: {spec['alias']}")
        bits = net["bits"]
        if len(bits) != spec["width"] or len(set(bits)) != len(bits) or not all(isinstance(b, int) for b in bits):
            raise ValueError(f"Unexpected payload width/constants/aliases: {target_name}")
        if set(bits).intersection(inputs | state_bits | selected_bits):
            raise ValueError(f"Payload intersects input/state/another cut: {target_name}")
        bad_aliases = sorted({n for b in bits for n in protected.get(b, [])})
        if bad_aliases:
            raise ValueError(f"Payload aliases protected protocol/control signal: {target_name}: {bad_aliases}")
        ds = [drivers.get(b, []) for b in bits]
        if any(len(d) != 1 for d in ds) or len({d[0] for d in ds}) != 1:
            raise ValueError(f"Payload does not have one unique driver: {target_name}")
        cell_name, port = ds[0][0]
        cell = original["cells"][cell_name]
        outputs = {p for p, direction in cell["port_directions"].items() if direction == "output"}
        if (cell["type"] not in ALLOWED_DRIVERS or outputs != {"Y"} or port != "Y"
                or cell["connections"]["Y"] != bits or cell_name in selected_cells):
            raise ValueError(f"Refuse partial, reordered, packed, sequential or unsupported driver: {target_name}")
        if spec["source_suffix"] not in cell.get("attributes", {}).get("src", ""):
            raise ValueError(f"Driver is not from audited source module: {target_name}")
        selected.append({"target": target_name, **spec, "original_cell_name": cell_name,
                         "original_cell": copy.deepcopy(cell), "output_bits": list(bits),
                         "overlapping_aliases": sorted(n for n, v in original["netnames"].items() if set(bits).intersection(v["bits"]))})
        selected_cells.add(cell_name)
        selected_bits.update(bits)

    result = copy.deepcopy(design)
    module = result["modules"][top]
    for cut in selected:
        del module["cells"][cut["original_cell_name"]]
        cut["replacement_cell_name"] = PREFIX + cut["target"]
        module["cells"][cut["replacement_cell_name"]] = {
            "hide_name": 1, "type": "$anyseq", "parameters": {"WIDTH": format(cut["width"], "032b")},
            "attributes": {"pscorr_proof_only": 1, "pscorr_abstraction_target": cut["target"],
                           "src": cut["original_cell"]["attributes"]["src"]},
            "port_directions": {"Y": "output"}, "connections": {"Y": cut["output_bits"]},
        }
    # Every object outside the exact driver substitutions must remain identical.
    for key in set(original) | set(module):
        if key != "cells" and original.get(key) != module.get(key):
            raise AssertionError(f"Unexpected module mutation: {key}")
    for name, cell in original["cells"].items():
        if name not in selected_cells and module["cells"].get(name) != cell:
            raise AssertionError(f"Unexpected native cell mutation: {name}")
    if len(module["cells"]) != len(original["cells"]):
        raise AssertionError("Each driver must have exactly one symbolic replacement")
    audit = {
        "scope": "PROOF ONLY: combinational overapproximation, never an implementation or optimization candidate",
        "mode": mode, "top": top, "original_structural_sha256": canonical_hash(design),
        "abstract_structural_sha256": canonical_hash(result), "cuts": selected,
        "fresh_symbolic_bits_per_cycle": sum(c["width"] for c in selected),
        "ports_unchanged": True, "netnames_and_aliases_unchanged": True,
        "all_native_state_cells_and_connections_unchanged": True,
        "native_cells_removed": sorted(selected_cells),
        "soundness_argument": "For any original state/input trace, choose each fresh anyseq payload equal to its removed combinational driver's original value at every step. All retained equations and native next-state then agree. Thus every original behavior is included; universal safety on the abstraction implies safety on the original model under the same external environment.",
        "limitations": "Counterexamples may be spurious. Arithmetic-value correlations, and optionally branch outcome restrictions, are relaxed. This artifact must not be physically mapped or credited as storage/area savings. No internal occupancy, readiness, fairness or latency premise is added.",
    }
    return result, audit


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--top", default="datapath")
    parser.add_argument("--mode", choices=MODES, default="alu_mul")
    args = parser.parse_args()
    if args.output.exists() or args.manifest.exists():
        parser.error("Use fresh output paths; proof artifacts are not overwritten")
    source = args.input.read_bytes()
    result, audit = abstract_datapath(json.loads(source), args.top, args.mode)
    audit["source_file_sha256"] = hashlib.sha256(source).hexdigest()
    audit["helper_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.manifest.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result) + "\n")
    audit["output_file_sha256"] = hashlib.sha256(args.output.read_bytes()).hexdigest()
    args.manifest.write_text(json.dumps(audit, indent=2) + "\n")
    print(json.dumps({"mode": args.mode, "proof_only": True, "symbolic_bits": audit["fresh_symbolic_bits_per_cycle"]}))


if __name__ == "__main__":
    main()
