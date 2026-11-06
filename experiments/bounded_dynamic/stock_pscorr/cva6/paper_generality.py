#!/usr/bin/env python3
"""Tabulate CVA6 runs of the paper's 21 workloads in the schema of rocket_generality.csv.

For each workload: mapped cell area of the workload-constrained core, the area of the
full-RV32IM (GP) core of the same flow, and the sweeping time, i.e. scorr's own TOTAL
time from the ABC log (the quantity the Rocket CSV records). Labels follow the Rocket CSV.
"""
from __future__ import annotations

import argparse
import csv
import json
import math
import re
from pathlib import Path

ROCKET_CSV = Path("/home/allenjin/Projects/DAC_pscorr/Overleaf/DAC-2026-PSCORR/src/figures/rocket_generality.csv")


def scorr_total(log: Path) -> float:
    m = re.findall(r"^TOTAL\s*=\s*([0-9.]+) sec", log.read_text(), re.M)
    if not m:
        raise SystemExit(f"no scorr TOTAL in {log}")
    return float(m[-1])


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--runs", type=Path, nargs="+", required=True,
                    help="directories with one run per workload (searched in order)")
    ap.add_argument("--gp", type=Path, help="full-RV32IM run (default: <first --runs>/gp)")
    ap.add_argument("--reference-csv", type=Path, default=ROCKET_CSV, help="workload order and labels")
    ap.add_argument("--csv", type=Path, required=True)
    ap.add_argument("--json", type=Path)
    args = ap.parse_args()
    rocket = list(csv.DictReader(args.reference_csv.open()))
    gp_dir = args.gp or args.runs[0] / "gp"
    gp = json.loads((gp_dir / "summary.json").read_text())
    rows, ratios = [], []
    for r in rocket:
        run = next(d / r["workload"] for d in args.runs if (d / r["workload"] / "summary.json").exists())
        s = json.loads((run / "summary.json").read_text())
        assert s["status"] == "ok" and s["flow"] == gp["flow"] and s["depth"] == gp["depth"]
        rows.append({"workload": r["workload"], "label": r["label"], "area_um2": s["cell_area"],
                     "reference_area_um2": gp["cell_area"], "sweeping_seconds": round(scorr_total(run / "abc.log"), 2)})
        ratios.append(s["cell_area"] / gp["cell_area"])
    with args.csv.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0]))
        w.writeheader()
        w.writerows(rows)
    t = sorted(r["sweeping_seconds"] for r in rows)
    geo = math.exp(sum(map(math.log, ratios)) / len(ratios))
    summary = {"flow": gp["flow"], "depth": gp["depth"], "workloads": len(rows), "gp_area_um2": gp["cell_area"],
               "gp_run": str(gp_dir), "gp_sweeping_seconds": scorr_total(gp_dir / "abc.log"),
               "geomean_normalized_area": geo, "geomean_reduction_pct": 100 * (1 - geo),
               "max_reduction_pct": 100 * (1 - min(ratios)), "min_reduction_pct": 100 * (1 - max(ratios)),
               "sweeping_seconds_median": t[len(t) // 2], "sweeping_seconds_max": t[-1]}
    if args.json:
        args.json.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
