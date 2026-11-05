#!/usr/bin/env python3
"""Discover guarded bank equalities from native write-enable control cones.

No phase name or enum value is supplied. Existing predicates on the closest
small control register are candidates; BMC may reject them, and only a joint
unbounded proof of every surviving assertion can certify the rewrite.
"""
from __future__ import annotations
import argparse
from collections import deque
import copy
import hashlib
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
sys.path.insert(0, str(ROOT))
from odc.temporal import checked_yosys, digest, proof_passed, run_command, validate_single_clock, yosys_path

SEQUENTIAL = {"$adff", "$adffe", "$dff", "$dffe", "$sdff", "$sdffe", "$sdffce"}


def discover_guards(design, top, bank, *, max_control_width=8, control_limit=1):
    m = design["modules"][top]
    driver, qdriver = {}, {}
    for name, cell in m["cells"].items():
        for port, direction in cell["port_directions"].items():
            if direction == "output":
                for bit in cell["connections"][port]:
                    if isinstance(bit, int):
                        if bit in driver:
                            raise ValueError("Multiple cell drivers")
                        driver[bit] = (name, cell)
        if cell["type"] in SEQUENTIAL:
            qdriver.update((q, (name, cell)) for q in cell["connections"]["Q"])
    distances = []
    for root in (bank["reference_a_enable"], bank["reference_b_enable"]):
        queue, visited, found = deque((b, 0) for b in root), set(), {}
        while queue:
            bit, distance = queue.popleft()
            if not isinstance(bit, int) or bit in visited:
                continue
            visited.add(bit)
            if bit in qdriver:
                name, cell = qdriver[bit]
                if len(cell["connections"]["Q"]) <= max_control_width:
                    found[name] = min(found.get(name, distance), distance)
                continue  # never cross a sequential boundary
            if bit in driver:
                _, cell = driver[bit]
                queue.extend((b, distance + 1) for port, direction in cell["port_directions"].items()
                             if direction == "input" for b in cell["connections"][port])
        distances.append(found)
    ranked = sorted(set(distances[0]) & set(distances[1]),
        key=lambda n: (max(d[n] for d in distances), sum(d[n] for d in distances), n))
    selected = ranked[:control_limit]
    controls = [{"cell": n, "q": m["cells"][n]["connections"]["Q"],
                 "enable_distances": [d[n] for d in distances]} for n in ranked]
    predicates, seen = [], set()
    for control in selected:
        q = set(m["cells"][control]["connections"]["Q"])
        for name, cell in sorted(m["cells"].items()):
            if cell["type"] not in ("$eq", "$logic_not") or len(cell["connections"]["Y"]) != 1:
                continue
            inputs = {p: bs for p, bs in cell["connections"].items() if cell["port_directions"][p] == "input"}
            variables = {b for bs in inputs.values() for b in bs if isinstance(b, int)}
            constants = [b for bs in inputs.values() for b in bs if isinstance(b, str)]
            if not variables or not variables <= q or any(b not in ("0", "1") for b in constants):
                continue
            if cell["type"] == "$eq" and not any(all(isinstance(b, str) for b in bs) for bs in inputs.values()):
                continue
            key = json.dumps([cell["type"], cell["parameters"], inputs], sort_keys=True)
            if key in seen:
                continue
            seen.add(key)
            predicates.append({"cell": name, "type": cell["type"], "parameters": cell["parameters"],
                               "inputs": inputs, "guard_bit": cell["connections"]["Y"][0], "control_cell": control})
    guards = []
    for i, predicate in enumerate(predicates):
        for side in ("a", "b"):
            guards.append({"id": f"guard_{i:03d}_{side}", "bank_side": side,
                           "reference_q": bank[f"reference_{side}_q"],
                           "shared_q": bank["candidate_shared_q"], **predicate})
    return {"ranked_controls": controls, "selected_controls": selected,
            "ranking": "minimum maximum, then summed combinational distance from BOTH original enabled-bank write events",
            "max_control_width": max_control_width, "control_limit": control_limit,
            "candidates": guards, "assumptions_added": 0}


def add_guard_assertions(design, top, guards, *, guard_only=False):
    out = copy.deepcopy(design)
    m = out["modules"][top]
    if guard_only:
        m["cells"] = {n: c for n, c in m["cells"].items() if c["type"] != "$assert"}
    used = {b for c in m["cells"].values() for bs in c["connections"].values() for b in bs if isinstance(b, int)}
    nextbit = max(used, default=1) + 1
    equality = {}
    for guard in guards:
        key = (tuple(guard["reference_q"]), tuple(guard["shared_q"]))
        if key not in equality:
            bit = nextbit
            nextbit += 1
            equality[key] = bit
            name = "$pscorr_guard_equal_" + str(len(equality))
            if name in m["cells"]:
                raise ValueError("Guard instrumentation already present")
            m["cells"][name] = {"type": "$eq", "hide_name": 1, "attributes": {},
                "parameters": {"A_SIGNED": 0, "B_SIGNED": 0, "A_WIDTH": len(key[0]), "B_WIDTH": len(key[1]), "Y_WIDTH": 1},
                "port_directions": {"A": "input", "B": "input", "Y": "output"},
                "connections": {"A": list(key[0]), "B": list(key[1]), "Y": [bit]}}
        m["cells"]["$pscorr_" + guard["id"]] = {"type": "$assert", "hide_name": 1,
            "attributes": {"src": "guard_candidate:" + guard["id"]}, "parameters": {},
            "port_directions": {"A": "input", "EN": "input"},
            "connections": {"A": [equality[key]], "EN": [guard["guard_bit"]]}}
    return out


def export_smt(design, top, directory, yosys):
    directory.mkdir()
    source, lowered, smt = directory / "native.json", directory / "lowered.json", directory / "model.smt2"
    source.write_text(json.dumps(design) + "\n")
    run = checked_yosys(yosys,
        f"read_json {yosys_path(source)}\ncheck -assert\nasync2sync\ndffunmap\nopt_clean\n"
        f"write_json {yosys_path(lowered)}\nwrite_smt2 -wires {yosys_path(smt)}\n", directory, "export", 60)
    lowered_design = json.loads(lowered.read_text())
    clock = validate_single_clock(lowered_design, top)
    cells = lowered_design["modules"][top]["cells"]
    return smt, {"export": run, "native_sha256": digest(source), "smt_sha256": digest(smt), "clock": clock,
                 "property_counts": {t: sum(c["type"] == "$" + t for c in cells.values()) for t in ("assert", "assume")}}


def rejected_guards(log, valid_ids):
    rejected = set()
    for line in log.splitlines():
        if "Assert failed" not in line:
            continue
        ids = set(re.findall(r"guard_\d{3}_[ab]", line))
        if not ids or not ids <= valid_ids:
            raise ValueError("BMC failure was not attributed to a generated guard")
        rejected.update(ids)
    return rejected


def main():
    workspace = next(p for p in HERE.parents if (p / "tools/oss-cad-suite-20261104").exists())
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--source-proof", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--bmc-depth", type=int, default=14)
    p.add_argument("--depth", type=int, default=3)
    p.add_argument("--timeout", type=int, default=120)
    p.add_argument("--control-limit", type=int, default=1)
    args = p.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True)
    source = args.source_proof.resolve()
    native_path = source / "native.json"
    original = json.loads(native_path.read_text())
    prior = json.loads((source / "proof.json").read_text())
    if not (prior.get("common_state_factoring") and prior.get("coherent_alu_abstraction")):
        raise ValueError("Expected certified factored/coherent native proof model")
    top = "BankMiter"
    discovery = discover_guards(original, top, prior["last_writer_certificate"], control_limit=args.control_limit)
    (out / "discovery.json").write_text(json.dumps(discovery, indent=2) + "\n")
    (out / "guard_invariants_source.py").write_bytes(Path(__file__).read_bytes())
    summary = {"status": "running", "proven": False, "source_proof_sha256": digest(source / "proof.json"),
        "source_native_sha256": digest(native_path), "implementation_sha256": digest(Path(__file__)),
        "assumptions_added": 0, "candidate_count": len(discovery["candidates"]),
        "premise": "Unchanged prior native-reset/environment; candidates are asserted, never assumed"}
    def save():
        (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    save()
    yosys = str(workspace / "tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys")
    smtbmc = str(Path(yosys).parent / "yosys-smtbmc")
    guards = discovery["candidates"]
    if not guards:
        summary["status"] = "no_structural_guards"
        save()
        return
    smt, meta = export_smt(add_guard_assertions(original, top, guards, guard_only=True), top, out / "screen", yosys)
    screen = run_command([smtbmc, "-s", "z3", "-t", str(args.bmc_depth), "--noprogress", "--keep-going",
        "--dump-vcd", str(out / "screen/failed_%.vcd"), str(smt)], out / "screen/bmc.log", args.timeout)
    rejected = rejected_guards(Path(screen["log"]).read_text(), {g["id"] for g in guards})
    guards = [g for g in guards if g["id"] not in rejected]
    summary["screen"] = {**meta, "run": screen, "rejected": sorted(rejected),
                          "survivors": [g["id"] for g in guards],
                          "scope": "BMC-only rejection in the reduced proof model, never an invariant certificate"}
    save()
    if not guards:
        summary["status"] = "all_guards_rejected"
        save()
        return
    smt, meta = export_smt(add_guard_assertions(original, top, guards), top, out / "joint", yosys)
    command = [smtbmc, "-s", "z3", "-t", str(args.depth), "--noprogress"]
    summary["joint"] = meta
    base = run_command(command + ["--dump-vcd", str(out / "joint/base.vcd"), str(smt)], out / "joint/base.log", args.timeout)
    summary["joint"]["base"] = base
    save()
    if proof_passed(base):
        step = run_command(command + ["-i", "--dump-vcd", str(out / "joint/step.vcd"), str(smt)], out / "joint/step.log", args.timeout)
        summary["joint"]["induction"] = step
        summary["proven"] = proof_passed(step)
    summary["status"] = "joint_unbounded_certificate" if summary["proven"] else "joint_not_proven"
    if digest(native_path) != summary["source_native_sha256"] or digest(Path(__file__)) != summary["implementation_sha256"]:
        summary["proven"] = False
        summary["status"] = "source_changed_during_proof"
    save()
    print(json.dumps({"status": summary["status"], "candidates": summary["candidate_count"],
                      "rejected": len(rejected), "survivors": len(guards)}))


if __name__ == "__main__":
    main()
