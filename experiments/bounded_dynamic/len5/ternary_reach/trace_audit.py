#!/usr/bin/env python3
"""Compare the ternary main trajectory with recorded native RTL simulation.

The simulation holds reset for several cycles; the formal model releases it
after one frame. A single constant cycle offset, fitted from the first accepted
fetch, must align every recorded ALU RS admission (cycle and native row index),
accepted fetch handshake (cycle and address, including requests later flushed),
flush, accepted store (cycle and address), and load request (cycle) inside the
simulated window, in both directions. The ternary trajectory must be fully
binary on these observation outputs.
"""
from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[3]))
from odc.temporal import digest  # noqa: E402


def rows(path: Path) -> list[dict]:
    with path.open() as f:
        return list(csv.DictReader(f))


def compare(name: str, simulated: list[tuple], formal: list[tuple], window: int) -> dict:
    formal_in = [e for e in formal if e[0] <= window]
    sim_set, formal_set = set(simulated), set(formal_in)
    return {"name": name, "simulated": len(simulated), "formal_in_window": len(formal_in),
            "match": sim_set == formal_set and len(sim_set) == len(simulated) == len(formal_in),
            "only_simulated": sorted(sim_set - formal_set)[:5], "only_formal": sorted(formal_set - sim_set)[:5]}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--reach", type=Path, required=True, help="reach.py output directory")
    ap.add_argument("--evidence", type=Path, required=True, help="Recorded platform simulation evidence")
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    trace = rows(args.reach / "trace.csv")
    if any(v == "x" for r in trace for v in r.values()):
        raise ValueError("Ternary main trajectory is not binary on the audited outputs")
    ev = args.evidence
    edges = rows(ev / "platform_edges.csv")
    live = [r for r in edges if r["reset_n"] == "1"]
    fetch = [(int(r["cycle"]), int(r["fetch_addr"])) for r in live if r["core_req"] == "1" and r["core_gnt"] == "1"]
    offset = fetch[0][0] - min(int(r["frame"]) for r in trace if r["obs_fetch"] == "1")
    window = max(int(r["cycle"]) for r in edges) - offset
    sim = {
        "alu_rs_admissions": [(int(r["cycle_pre_edge"]) - offset, int(r["new_idx"]))
                              for r in rows(ev / "occupancy.csv") if r["insert"] == "1"],
        "fetch_requests": [(c - offset, a) for c, a in fetch],
        "flushes": [(int(r["cycle"]) - offset,) for r in live if r["flush"] == "1"],
        "stores": [((int(r["time"]) - 1) // 2 - offset, int(r["data_store_addr_o"]))
                   for r in rows(ev / "accepted_stores.csv")],
        "load_requests": [(int(r["request_cycle"]) - offset,) for r in rows(ev / "load_responses.csv")],
    }
    formal = {
        "alu_rs_admissions": [(int(r["frame"]), int(r["obs_index"])) for r in trace if r["obs_insert"] == "1"],
        "fetch_requests": [(int(r["frame"]), int(r["obs_fetch_addr"])) for r in trace if r["obs_fetch"] == "1"],
        "flushes": [(int(r["frame"]),) for r in trace if r["obs_flush"] == "1"],
        "stores": [(int(r["frame"]), int(r["obs_store_addr"])) for r in trace if r["obs_store"] == "1"],
        "load_requests": [(int(r["frame"]),) for r in trace if r["obs_load"] == "1"],
    }
    results = [compare(k, sim[k], formal[k], window) for k in sim]
    reach = json.loads((args.reach / "summary.json").read_text())
    record = {
        "status": "matched" if all(r["match"] for r in results) else "mismatch",
        "reach_summary_sha256": digest(args.reach / "summary.json"), "trace_sha256": digest(args.reach / "trace.csv"),
        "evidence": str(args.evidence.resolve()),
        "evidence_sha256": {p: digest(ev / p) for p in ("fetch_responses.csv", "occupancy.csv", "accepted_stores.csv",
                                                        "load_responses.csv", "platform_edges.csv")},
        "gap": reach["instruction_acceptance_gap"], "cycle_offset": offset, "window_frames": window,
        "comparisons": results,
        "formal_alu_rows_admitted_in_window": sorted({i for t, i in formal["alu_rs_admissions"] if t <= window}),
        "formal_alu_rows_admitted_all_frames": sorted({i for _, i in formal["alu_rs_admissions"]}),
        "script_sha256": digest(Path(__file__)),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({k: record[k] for k in ("status", "gap", "cycle_offset", "window_frames",
                                             "formal_alu_rows_admitted_all_frames")}))
    for r in results:
        print(json.dumps(r))
    return 0 if record["status"] == "matched" else 1


if __name__ == "__main__":
    raise SystemExit(main())
