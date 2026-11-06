#!/usr/bin/env python3
"""Tabulate Pscorr runs (run_len5.py / run_cva6.py summaries) under a build root.

Prints one row per run: flow, depth, CRISP file, AIG sizes before and after ABC,
scorr time, mapped cell area and cells, and the reduction relative to the named
reference runs (unconstrained and full-ISA, same flow and depth).
"""
from __future__ import annotations

import argparse
import csv
import json
import sys
from pathlib import Path


def load(run: Path) -> dict | None:
    s = run / "summary.json"
    if not s.exists():
        return None
    r = json.loads(s.read_text())
    r["run"] = str(run)
    return r


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--runs", type=Path, nargs="+", required=True)
    ap.add_argument("--reference", type=Path, required=True, help="unconstrained run or a gate map with a log")
    ap.add_argument("--isa-reference", type=Path, help="full-ISA run")
    ap.add_argument("--csv", type=Path)
    args = ap.parse_args()

    def area_of(p: Path):
        r = load(p)
        if r and r.get("cell_area"):
            return r["cell_area"]
        log = p / "gates_run.log"
        import re
        m = re.findall(r"Chip area for (?:top )?module '[^']*':\s*([0-9.]+)", log.read_text()) if log.exists() else []
        return float(m[-1]) if m else None

    a0 = area_of(args.reference)
    ai = area_of(args.isa_reference) if args.isa_reference else None
    rows = []
    for run in args.runs:
        r = load(run)
        if not r:
            print(f"{run}: no summary yet", file=sys.stderr)
            continue
        area = r.get("cell_area")
        rows.append({
            "run": run.name, "flow": r.get("flow", "stock"), "depth": r["depth"],
            "crisp": Path(r["dsl"]).name if r.get("dsl") else "-",
            "latches_before": r["yosys_aig"]["lat"], "ands_before": r["yosys_aig"]["and"],
            "constraints": r["yosys_aig"]["c"],
            "latches_after": r["post_abc"]["lat"] if r.get("post_abc") else None,
            "ands_after": r["post_abc"]["and"] if r.get("post_abc") else None,
            "abc_seconds": r.get("abc_seconds"), "cell_area": area, "cells": r.get("cells"),
            "reduction_vs_reference_pct": round(100 * (1 - area / a0), 4) if area and a0 else None,
            "reduction_vs_isa_reference_pct": round(100 * (1 - area / ai), 4) if area and ai else None,
        })
    for row in rows:
        print(json.dumps(row))
    if args.csv and rows:
        with open(args.csv, "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(rows[0]))
            w.writeheader()
            w.writerows(rows)
    print(json.dumps({"reference_area": a0, "isa_reference_area": ai}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
