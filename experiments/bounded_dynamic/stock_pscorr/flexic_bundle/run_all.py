#!/usr/bin/env python3
"""Map every design in manifest.csv to one Liberty library and tabulate the areas.

    python3 run_all.py --liberty /path/to/flexic.lib [--jobs 4] [--out DIR] [--only rocket]

Writes DIR/results.csv (one row per design: area, its reference's area, normalized
area) and DIR/summary.txt (per-study geomean/min/max, as in the paper).
Re-running with the same --out reuses designs that already have an area.
Use --only to select designs whose id contains the given text (e.g. "ibex/").
"""
from __future__ import annotations

import argparse
import csv
import math
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

HERE = Path(__file__).resolve().parent
AREA_RE = re.compile(r"Chip area for (?:top )?module.*?:\s*([0-9.eE+-]+)")
UNMAPPED_RE = re.compile(r"^\s*\\\$_\w+", re.MULTILINE)


def area_from_log(log: Path):
    if not log.exists():
        return None
    found = AREA_RE.findall(log.read_text(errors="replace"))
    return float(found[-1]) if found else None


def run_one(row, liberty: Path, out: Path):
    prefix = out / "designs" / row["id"] / "mapped"
    area = area_from_log(prefix.with_suffix(".log"))
    if area is None:
        aig = HERE / "designs" / row["id"] / "optimized.aig"
        res = subprocess.run([str(HERE / "map_area.sh"), str(liberty), str(aig), row["top"], row["clock"], str(prefix)],
                             capture_output=True, text=True)
        if res.returncode != 0:
            return row["id"], None, res.stderr.strip()[-400:]
        area = area_from_log(prefix.with_suffix(".log"))
    gates = Path(str(prefix) + ".gates.v")
    unmapped = sorted(set(m.strip() for m in UNMAPPED_RE.findall(gates.read_text()))) if gates.exists() else []
    return row["id"], area, ("unmapped cells: " + " ".join(unmapped)) if unmapped else ""


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--liberty", type=Path, required=True)
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--out", type=Path)
    ap.add_argument("--only", default="")
    args = ap.parse_args()
    liberty = args.liberty.resolve()
    if not liberty.exists():
        sys.exit(f"no such Liberty file: {liberty}")
    out = (args.out or Path.cwd() / f"results_{liberty.stem}").resolve()
    out.mkdir(parents=True, exist_ok=True)
    with (HERE / "manifest.csv").open(newline="") as f:
        rows = [r for r in csv.DictReader(f) if args.only in r["id"]]
    ids = {r["id"] for r in rows}
    # A selected workload needs its reference too.
    with (HERE / "manifest.csv").open(newline="") as f:
        allrows = {r["id"]: r for r in csv.DictReader(f)}
    for r in list(rows):
        if r["reference_id"] and r["reference_id"] not in ids:
            rows.append(allrows[r["reference_id"]]); ids.add(r["reference_id"])
    print(f"{len(rows)} designs, liberty {liberty}, {args.jobs} jobs -> {out}", flush=True)
    area, note = {}, {}
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = [pool.submit(run_one, r, liberty, out) for r in rows]
        for i, fut in enumerate(as_completed(futures), 1):
            rid, a, msg = fut.result()
            area[rid], note[rid] = a, msg
            print(f"[{i}/{len(rows)}] {rid}: {a if a is not None else 'FAILED'} {msg}", flush=True)
    fields = ["id", "core", "study", "label", "role", "area", "reference_id", "reference_area", "normalized_area",
              "sky130_area_um2_recorded", "note"]
    table = []
    for r in rows:
        a, ref = area.get(r["id"]), r["reference_id"]
        ra = area.get(ref) if ref else None
        table.append({"id": r["id"], "core": r["core"], "study": r["study"], "label": r["label"], "role": r["role"],
                      "area": a, "reference_id": ref, "reference_area": ra,
                      "normalized_area": (a / ra) if (a and ra) else "",
                      "sky130_area_um2_recorded": r["sky130_area_um2"], "note": note.get(r["id"], "")})
    with (out / "results.csv").open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        w.writerows(table)
    lines = [f"Liberty: {liberty}", f"Area unit: as defined by the Liberty file (SKY130: um^2)", ""]
    for core, study in sorted({(t["core"], t["study"]) for t in table}):
        group = [t for t in table if (t["core"], t["study"]) == (core, study) and t["normalized_area"] != ""]
        if not group:
            continue
        norm = [t["normalized_area"] for t in group]
        geo = math.exp(sum(math.log(x) for x in norm) / len(norm))
        lines.append(f"{core} / {study}: {len(group)} designs")
        if study == "table4_timing":
            for t in group:
                lines.append(f"  {t['label']:<26s} {t['area']:.4f} vs {t['reference_area']:.4f} without timing: "
                             f"{100 * (1 - t['normalized_area']):.2f}% reduction")
        else:
            refs = sorted({t["reference_area"] for t in group})
            lines.append(f"  RV32IM reference area: " + ", ".join(f"{x:.4f}" for x in refs))
            lines.append(f"  geomean reduction {100 * (1 - geo):.2f}%, max {100 * (1 - min(norm)):.2f}%, "
                         f"min {100 * (1 - max(norm)):.2f}%")
        lines.append("")
    failed = [t["id"] for t in table if t["area"] is None]
    flagged = [t["id"] for t in table if t["note"]]
    lines.append(f"failed: {len(failed)} {' '.join(failed)}")
    lines.append(f"flagged (see note column): {len(flagged)}")
    (out / "summary.txt").write_text("\n".join(lines) + "\n")
    print("\n".join(lines))
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
