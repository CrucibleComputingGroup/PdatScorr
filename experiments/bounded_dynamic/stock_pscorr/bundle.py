#!/usr/bin/env python3
"""Copy the small records of finished runs into a hash-checked evidence directory.

Kept per run: summary.json, generated assumptions (assumptions*.sv, inject_*.sv),
the Yosys script, codegen.log, abc.log and the chip-area lines of gates_run.log.
Kept per validation: summary.json, spec*.txt, sim*.json and sim.log. AIGs, netlists
and full logs stay at their build paths and are listed with size and SHA-256.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
from pathlib import Path

KEEP = ("summary.json", "synth.ys", "codegen.log", "abc.log", "spec.txt", "spec_aligned.txt", "spec_random.txt",
        "spec_axi2.txt", "sim.log", "sim.json", "sim_aligned.json", "sim_random.json", "sim_axi2.json", "aig_stats.txt")


def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--runs", type=Path, nargs="+", required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    out = args.output
    out.mkdir(parents=True, exist_ok=False)
    omitted = []
    for run in args.runs:
        dst = out / run.name
        dst.mkdir()
        for f in sorted(run.iterdir()):
            if not f.is_file():
                continue
            if f.name in KEEP or f.suffix == ".jsonl" or f.name.startswith("assumptions") or f.name.startswith("inject_"):
                shutil.copyfile(f, dst / f.name)
            elif f.name == "gates_run.log":
                lines = [l for l in f.read_text(errors="replace").splitlines() if re.search(r"Chip area|Number of cells", l)]
                (dst / "gates_area.txt").write_text("\n".join(lines[-2:]) + "\n")
                omitted.append((str(f), f.stat().st_size, sha(f)))
            else:
                omitted.append((str(f), f.stat().st_size, sha(f)))
    (out / "omitted_files.tsv").write_text("".join(f"{p}\t{s}\t{h}\n" for p, s, h in omitted))
    sums = [f"{sha(p)}  {p.relative_to(out)}" for p in sorted(out.rglob("*")) if p.is_file()]
    (out / "SHA256SUMS").write_text("\n".join(sums) + "\n")
    print(json.dumps({"runs": len(args.runs), "files": len(sums), "omitted": len(omitted)}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
