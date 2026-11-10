#!/usr/bin/env python3
"""Compare regenerated Ibex Fig. 3 runs with the values recorded for the paper.

    tabulate.py [OUT]                 check the 13 designs; writes OUT/results.csv
    tabulate.py --forms DIR [WIDTH]   tabulate the data-width forms tried in
                                      DIR/data_width/<form>/width<WIDTH>; writes
                                      DIR/width_forms.csv (WIDTH defaults to 8)

Two register-count designs are known not to reproduce the paper's record exactly
(build_bundle.IBEX_FIG3_DEVIATIONS). Exits non-zero if any other design differs from the
paper in AND count, SKY130 area or FMax, or if those two differ from their documented values.
"""
from __future__ import annotations

import csv
import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from build_bundle import IBEX_FIG3, IBEX_FIG3_DEVIATIONS, IBEX_FIG3_OUT, STD  # noqa: E402

# FMax in MHz as recorded for the paper's figure (precision as recorded).
PAPER_FMAX = {
    "fig3_regs_32": "26.90", "fig3_regs_16": "38.32", "fig3_regs_08": "44.39", "fig3_regs_04": "48.45",
    "fig3_isa_rv32im": "22.0", "fig3_isa_rv32i": "26.9", "fig3_isa_no_shifts": "28.5",
    "fig3_isa_no_branches": "27.5", "fig3_isa_arith_only": "27.9",
    "fig3_width_32": "27.10", "fig3_width_24": "32.01", "fig3_width_16": "39.19", "fig3_width_08": "44.32",
}
# FMax of the regenerated netlists that differ from the paper's record.
DEVIATION_FMAX = {"fig3_regs_08": "44.43", "fig3_regs_04": "48.45"}


def metrics(run: Path, prefix: str):
    aig = run / f"{prefix}_post_abc.aig"
    with aig.open("rb") as f:
        ands = int(f.readline().split()[5])  # AIGER header: aig M I L O A
    area = float((run / f"{prefix}_total_area.txt").read_text().split()[0])
    fmax = json.loads((run / f"{prefix}_timing_metrics.json").read_text())["max_frequency_mhz"]
    return ands, area, float(fmax), hashlib.sha256(aig.read_bytes()).hexdigest()


def same_fmax(fmax: float, paper: str) -> bool:
    return f"{fmax:.{len(paper.split('.')[1])}f}" == paper


def check(out: Path) -> int:
    rows, bad = [], 0
    for design, study, label, _ref, run, prefix, paper_ands, paper_area in IBEX_FIG3:
        ands, area, fmax, digest = metrics(out / run, prefix)
        ok = ands == paper_ands and abs(area - paper_area) <= 0.05 and same_fmax(fmax, PAPER_FMAX[design])
        status = "yes"
        if not ok:
            want_ands, want_area = IBEX_FIG3_DEVIATIONS.get(design, (None, 0.0))
            documented = (ands == want_ands and abs(area - want_area) <= 0.05
                          and same_fmax(fmax, DEVIATION_FMAX.get(design, "0.0")))
            status = "no (documented)" if documented else "NO (unexpected)"
            bad += not documented
        rows.append({"design": design, "study": study, "label": label,
                     "paper_and_gates": paper_ands, "and_gates": ands,
                     "paper_area_um2": paper_area, "area_um2": area,
                     "paper_fmax_mhz": PAPER_FMAX[design], "fmax_mhz": fmax,
                     "matches_paper": status, "aig_sha256": digest, "run": run})
    with (out / "results.csv").open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0]), lineterminator="\n")
        w.writeheader()
        w.writerows(rows)
    for r in rows:
        print(f"{r['label']:<12s} AND {r['and_gates']:>6d} (paper {r['paper_and_gates']:>6d})  "
              f"area {r['area_um2']:>12.4f} (paper {r['paper_area_um2']:>9.1f})  "
              f"FMax {r['fmax_mhz']:>6.2f} (paper {r['paper_fmax_mhz']:>5s})  {r['matches_paper']}")
    exact = sum(r["matches_paper"] == "yes" for r in rows)
    print(f"{exact} of {len(rows)} designs match the paper exactly; {bad} unexpected differences -> {out / 'results.csv'}")
    return 1 if bad else 0


def forms(folder: Path, width: int) -> int:
    target = next(t for t in IBEX_FIG3 if t[0] == f"fig3_width_{width:02d}")
    rows = []
    for run in sorted((folder / "data_width").glob(f"*/width{width:02d}")):
        if not (run / f"{STD}_total_area.txt").exists():
            continue
        ands, area, fmax, _ = metrics(run, STD)
        ok = ands == target[6] and abs(area - target[7]) <= 0.05 and same_fmax(fmax, PAPER_FMAX[target[0]])
        rows.append({"form": run.parent.name, "width": width, "and_gates": ands, "area_um2": area,
                     "fmax_mhz": fmax, "matches_paper": "yes" if ok else "no"})
    rows.sort(key=lambda r: (r["matches_paper"] != "yes", r["form"]))
    with (folder / "width_forms.csv").open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0]), lineterminator="\n")
        w.writeheader()
        w.writerows(rows)
    print(f"paper, {width}-bit: {target[6]} ANDs, {target[7]} um2, {PAPER_FMAX[target[0]]} MHz")
    for r in rows:
        print(f"{r['form']:<12s} {r['and_gates']:>6d} ANDs  {r['area_um2']:>12.4f} um2  {r['fmax_mhz']:>6.2f} MHz  "
              f"{r['matches_paper']}")
    return 0


def main() -> int:
    args = sys.argv[1:]
    if args and args[0] == "--forms":
        return forms(Path(args[1]), int(args[2]) if len(args) > 2 else 8)
    return check(Path(args[0]) if args else IBEX_FIG3_OUT)


if __name__ == "__main__":
    raise SystemExit(main())
