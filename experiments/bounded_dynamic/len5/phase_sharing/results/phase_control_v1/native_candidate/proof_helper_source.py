"""Proof-local, asserted congruence certificates for unchanged native state.

Discover matches BEFORE async2sync turns named Q nets into reset mux outputs.
Ambiguous aliases are excluded. Certificates are extra assertions, never
assumptions; the sole premise remains the miter's initial reset.
"""
from __future__ import annotations
import json
from pathlib import Path
import re

from odc.temporal import (checked_yosys, digest, formal_lower_command, proof_passed,
                          run_command, validate_single_clock, yosys_path)


def assert_native_correspondence(design, top):
    m = design["modules"][top]
    qbits = set()
    for cell in m["cells"].values():
        if cell["type"] in ("$dff", "$dffe", "$adff", "$adffe", "$sdff", "$sdffe", "$sdffce"):
            qbits.update(b for b in cell["connections"]["Q"] if isinstance(b, int))
        elif "ff" in cell["type"].lower() or "latch" in cell["type"].lower():
            raise ValueError("Unsupported native sequential cell")
    edges = set()
    for name, net in m["netnames"].items():
        if not name.startswith("candidate."):
            continue
        original = m["netnames"].get("reference." + name.removeprefix("candidate."))
        if original is None or len(original["bits"]) != len(net["bits"]):
            continue
        edges.update((r, c) for r, c in zip(original["bits"], net["bits"])
                     if r in qbits and c in qbits and r != c)
    from_ref, from_cand = {}, {}
    for r, c in edges:
        from_ref.setdefault(r, set()).add(c)
        from_cand.setdefault(c, set()).add(r)
    accepted = sorted((r, c) for r, c in edges if len(from_ref[r]) == len(from_cand[c]) == 1)
    ambiguous = sorted(edges - set(accepted))
    if not accepted:
        raise ValueError("No one-to-one native state matches")
    bit = max(b for cell in m["cells"].values() for bs in cell["connections"].values()
              for b in bs if isinstance(b, int)) + 1
    prefix = "$pscorr_native_congruence"
    if any(n.startswith(prefix) for n in m["cells"]):
        raise ValueError("State certificate already present")
    m["cells"][prefix + "_equal"] = {"hide_name": 1, "type": "$eq", "attributes": {},
        "parameters": {"A_SIGNED": 0, "B_SIGNED": 0, "A_WIDTH": len(accepted),
                       "B_WIDTH": len(accepted), "Y_WIDTH": 1},
        "port_directions": {"A": "input", "B": "input", "Y": "output"},
        "connections": {"A": [r for r, c in accepted], "B": [c for r, c in accepted], "Y": [bit]}}
    m["cells"][prefix + "_assert"] = {"hide_name": 1, "type": "$assert", "attributes": {},
        "parameters": {}, "port_directions": {"A": "input", "EN": "input"},
        "connections": {"A": [bit], "EN": ["1"]}}
    return {"asserted_state_pairs": len(accepted), "pairs": accepted,
            "excluded_ambiguous_edges": ambiguous, "excluded_edge_count": len(ambiguous),
            "assumptions_added": 0, "initial_pairing": False,
            "domain": "native Q equality asserted at all steps, lowered with native resets"}


def prove(reference, candidate, harness, directory, *, yosys, timeout=120,
          engine="induction", abc="/usr/local/bin/abc", depth=6):
    directory.mkdir()
    top = "BankMiter"
    hashes = {n: digest(p) for n, p in (("reference", reference), ("candidate", candidate),
                                        ("harness", harness), ("proof_helper", Path(__file__)))}
    (directory / "proof_helper_source.py").write_bytes(Path(__file__).read_bytes())
    result = {"proven": False, "method": "native-state-assertions-" + engine, "input_sha256": hashes,
              "initial_pairing": False, "state_assumptions_added": 0}
    try:
        native = directory / "native.json"
        result["prepare"] = checked_yosys(yosys,
            f"read_verilog -formal -sv {yosys_path(reference)} {yosys_path(candidate)} {yosys_path(harness)}\n"
            f"prep -top {top} -flatten\ncheck -assert\n" + formal_lower_command(yosys)
            + f"write_json {yosys_path(native)}\n", directory, "prepare", timeout)
        design = json.loads(native.read_text())
        result["native_state_certificates"] = assert_native_correspondence(design, top)
        native.write_text(json.dumps(design) + "\n")
        lowered = directory / "lowered.json"
        result["lower"] = checked_yosys(yosys,
            f"read_json {yosys_path(native)}\ncheck -assert\nasync2sync\ndffunmap\n"
            f"write_json {yosys_path(lowered)}\n", directory, "lower", timeout)
        lower = json.loads(lowered.read_text())
        result["clock_model"] = validate_single_clock(lower, top)
        result["property_counts"] = {t: sum(c["type"] == "$" + t for c in lower["modules"][top]["cells"].values())
                                     for t in ("assert", "assume", "cover")}
        if engine == "induction":
            smt = directory / "model.smt2"
            result["export"] = checked_yosys(yosys,
                f"read_json {yosys_path(lowered)}\nwrite_smt2 -wires {yosys_path(smt)}\n", directory, "export", timeout)
            smtbmc = str(Path(yosys).parent / "yosys-smtbmc")
            args = [smtbmc, "-s", "z3", "-t", str(depth), "--noprogress"]
            result["base"] = run_command(args + ["--dump-vcd", str(directory / "base.vcd"), str(smt)], directory / "base.log", timeout)
            if proof_passed(result["base"]):
                result["induction"] = run_command(args + ["-i", "--dump-vcd", str(directory / "step.vcd"), str(smt)], directory / "induction.log", timeout)
                result["proven"] = proof_passed(result["induction"])
        elif engine == "pdr":
            aig = directory / "model.aig"
            result["export"] = checked_yosys(yosys,
                f"read_json {yosys_path(lowered)}\nchformal -cover -remove\nformalff -clk2ff\n"
                "setundef -anyseq\nopt -keepdc\ntechmap\nopt -keepdc\nsetundef -anyseq\nabc -g AND\naigmap\n"
                f"write_aiger -zinit -symbols {yosys_path(aig)}\n", directory, "export", timeout)
            with aig.open("rb") as stream:
                header = stream.readline().decode("ascii").split()
            if (header[0] != "aig" or len(header) < 7 or int(header[4]) != 0
                    or int(header[6]) < 1 or any(int(x) for x in header[8:])):
                raise ValueError("Expected safety properties, no ordinary outputs/liveness")
            result["aig_bad_properties"] = int(header[6])
            result["aig_constraints"] = int(header[7]) if len(header) > 7 else 0
            command = f'read_aiger "{aig.resolve()}"; fold; orpos; pdr -T {int(timeout)} -v'
            result["pdr"] = run_command([abc, "-c", command], directory / "pdr.log", timeout + 5)
            log = (directory / "pdr.log").read_text()
            result["proven"] = (result["pdr"]["returncode"] == 0 and not result["pdr"]["timeout"]
                and len(re.findall(r"(?m)^Property proved\.", log)) == 1
                and not re.search(r"\b(error|failed|undecided|disproved|timed out|time limit|was asserted)\b", log, re.I))
            result["aig_sha256"] = digest(aig)
        else:
            raise ValueError("Unsupported proof engine")
    except (RuntimeError, ValueError, OSError) as e:
        result["error"] = str(e)
    for n, p in (("reference", reference), ("candidate", candidate), ("harness", harness), ("proof_helper", Path(__file__))):
        if digest(p) != hashes[n]:
            result["proven"] = False
            result["error"] = n + " changed during proof"
    (directory / "proof.json").write_text(json.dumps(result, indent=2) + "\n")
    return result
