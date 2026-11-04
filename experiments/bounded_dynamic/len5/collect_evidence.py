#!/usr/bin/env python3
"""Collect compact LEN5 qualification evidence, including failed attempts."""
from __future__ import annotations

import json
import csv
import re
from pathlib import Path

from prepare_frontend import digest, workspace_root


def find_ooo_witness(path: Path) -> dict:
    active, requests, records = {}, {}, []
    epoch = 0
    for row in csv.DictReader(path.open()):
        cycle, rob, kind = int(row["cycle"]), int(row["rob"]), row["event"]
        if kind in ("RESET", "FLUSH"):
            epoch += 1
            active.clear()
            requests.clear()
        elif kind == "DISPATCH":
            record = dict(sequence=len(records), epoch=epoch, dispatch_cycle=cycle, rob=rob,
                          pc=int(row["v0"], 16), instruction=int(row["v1"], 16))
            records.append(record)
            active[rob] = record
        elif kind in ("ALU_START", "ALU_RESULT"):
            assert rob in active, row
            active[rob][kind.lower() + "_cycle"] = cycle
            if kind == "ALU_RESULT":
                active[rob]["result"] = int(row["v0"], 16)
        elif kind == "LOAD_REQUEST":
            assert rob in active, row
            record = active[rob]
            record.update(request_cycle=cycle, memory_tag=int(row["v0"], 16), address=int(row["v1"], 16))
            requests[record["memory_tag"]] = record
        elif kind == "LOAD_RESPONSE":
            tag = int(row["v0"], 16)
            assert tag in requests, row
            requests.pop(tag).update(response_cycle=cycle, load_value=int(row["v1"], 16))
    def opcode(r): return r["instruction"] & 0x7f
    def rd(r): return (r["instruction"] >> 7) & 31
    def rs1(r): return (r["instruction"] >> 15) & 31
    def is_addi(r): return opcode(r) == 0x13 and (r["instruction"] >> 12) & 7 == 0
    witnesses = []
    for load in records:
        if opcode(load) != 3 or "response_cycle" not in load:
            continue
        for waiting in records[load["sequence"] + 1:]:
            if (not is_addi(waiting) or rs1(waiting) != rd(load) or "alu_start_cycle" not in waiting
                    or waiting["sequence"] != load["sequence"] + 1 or waiting["epoch"] != load["epoch"]):
                continue
            for younger in records[waiting["sequence"] + 1:]:
                if (not is_addi(younger) or rs1(younger) != 0 or "alu_result_cycle" not in younger
                        or younger["sequence"] != waiting["sequence"] + 1 or younger["epoch"] != load["epoch"]):
                    continue
                if (younger["alu_result_cycle"] < load["response_cycle"]
                        and younger["alu_start_cycle"] < waiting["alu_start_cycle"]
                        and load["dispatch_cycle"] < waiting["dispatch_cycle"] < younger["dispatch_cycle"]):
                    witnesses.append({"older_load": load, "older_dependent_alu": waiting, "younger_independent_alu": younger})
    return {"trace_sha256": digest(path.read_bytes()), "witness_found": bool(witnesses),
            "interpretation": "A younger independent ADDI reaches the actual ALU result handshake before an older load responds and starts execution before an older load-dependent ADDI. This is a finite trace of dynamic issue, not a correctness proof.",
            "witnesses": witnesses[:1]}


def main() -> None:
    here = Path(__file__).resolve().parent
    build_root = workspace_root(here) / "experiments/bounded_dynamic/len5/build"
    out = here / "results"
    out.mkdir(exist_ok=True)
    records = {}
    artifacts = {}
    names = ("integer_frontend", "pre_fpu_frontend", "pre_fpu_simulation",
             "pre_fpu_simulation_compat", "pre_fpu_simulation_host",
             "pre_fpu_simulation_pipe2", "pre_fpu_simulation_final", "pre_fpu_simulation_ooo")
    for name in names:
        src = build_root / name
        if not (src / "manifest.json").exists():
            continue
        m = json.loads((src / "manifest.json").read_text())
        dest = out / name
        dest.mkdir(exist_ok=True)
        keep = ("manifest.json", "frontend.ys", "sources.txt", "frontend.log", "check.ys",
                "check.log", "normalize.ys", "normalize.log", "build.log", "compile.log",
                "smoke.S", "smoke.hex", "run.log", "logs/sim-trace.log", "logs/qualification_events.csv")
        for rel in keep:
            p = src / rel
            if not p.exists():
                continue
            q = dest / rel
            q.parent.mkdir(parents=True, exist_ok=True)
            raw = p.read_bytes()
            q.write_bytes(raw)
            artifacts[str(q.relative_to(out))] = digest(raw)
        record = {k: m[k] for k in ("upstream_commit", "status", "returncode", "build_returncode",
                                    "run_returncode", "smoke_passed", "memory_pipe_num") if k in m}
        if (src / "run.log").exists():
            run = (src / "run.log").read_text()
            record["run_log_has_error"] = "ERROR" in run
            record["exit_zero_message"] = "Program exit with code: 0x00 (SUCCESS)" in run
            record["timeout"] = "timeout" in run.lower()
            for key, pattern in (("reported_cpu_cycles", r"total CPU cycles:\s+(\d+)"),
                                 ("reported_retired_instructions", r"retired instructions:\s+(\d+)"),
                                 ("memory_read_requests", r"read requests:\s+(\d+)")):
                match = re.search(pattern, run)
                record[key] = int(match.group(1)) if match else None
        records[name] = record
    fm = json.loads((build_root / "pre_fpu_frontend/manifest.json").read_text())
    sm = json.loads((build_root / "pre_fpu_simulation_ooo/manifest.json").read_text())
    assert fm["original_sha256"] == fm["prepared_sha256"]
    assert sm["frontend_manifest_sha256"] == digest((build_root / "pre_fpu_frontend/manifest.json").read_bytes())
    assert sm["capacity_parameters"] == fm["capacity_parameters_unchanged"]
    assert all(v == fm["prepared_sha256"][k.removeprefix("source/")]
               for k, v in sm["core_source_sha256"].items())
    assert len(sm["core_source_sha256"]) == fm["source_count"] == 74
    assert sm["qualification_monitor_sha256"] == digest((here / "qualification_monitor.svh").read_bytes())
    assert fm["normalized_structural_check"]["returncode"] == 0
    final = records["pre_fpu_simulation_ooo"]
    accepted = sm["smoke_passed"] and not final["run_log_has_error"] and not final["timeout"]
    witness = find_ooo_witness(build_root / "pre_fpu_simulation_ooo/logs/qualification_events.csv")
    accepted = accepted and witness["witness_found"] and final["memory_read_requests"] > 0
    (out / "ooo_witness.json").write_text(json.dumps(witness, indent=2) + "\n")
    summary = {
        "scope": "Source-grounded genuine OoO qualification, unchanged-RTL elaboration/structural check, and one self-checking smoke with execution-event tracing. No automatic ODC, area, or full-ISA correctness claim.",
        "qualified_source_commit": fm["upstream_commit"],
        "upstream_url": fm["upstream_url"],
        "qualified": accepted,
        "dynamic_ooo_witness": witness,
        "core_rtl_unchanged": True, "source_count": 74,
        "capacities": sm["capacity_parameters"], "fetch_fifo_depth": sm["fetch_fifo_depth"],
        "baseline_memory_pipe_num": sm["memory_pipe_num"],
        "known_limits": [
            "Three frontend missing-reset-value warnings retained; no sequential correctness proof.",
            "Current FPU-merge revision has an unresolved FCSR multi-driver conflict; selected official pre-FPU revision avoids it without a functional patch.",
            "Historical pipe2 smoke had exit0 but a broken upstream static trace variable caused monitor ERRORs; its old smoke_passed flag alone is not accepted qualification.",
            "A zero-stage memory run with the nonbypass two-entry fetch FIFO failed; preserve fixed capacity and a compatible minimum instruction-response latency.",
            "Smoke exercises integer loop, branch, store forwarding, and a preinitialized memory load; multiply/divide and full software regression remain unqualified.",
        ],
        "attempts": records,
        "driver_script_sha256": {p.name: digest(p.read_bytes()) for p in
                                  (here / "prepare_frontend.py", here / "qualify_simulation.py", Path(__file__))},
        "documentation_sha256": {p.name: digest(p.read_bytes()) for p in
                                  (here / "README.md", here / "CANDIDATE_REVIEW.md")},
        "artifact_sha256": artifacts,
    }
    (out / "qualification.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({"qualified": accepted, "final": final}))
    if not accepted:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
