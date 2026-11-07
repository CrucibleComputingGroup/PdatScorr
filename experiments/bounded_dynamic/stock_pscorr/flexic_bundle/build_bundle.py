#!/usr/bin/env python3
"""Assemble the FlexIC area bundle: the paper's Pscorr-optimized netlists for
Rocket, CVA6 and Ibex, a technology-mapping script that takes any Liberty file,
and a manifest with the recorded SKY130 areas.

Each design is copied from the archived run that produced the paper's number,
and its AIG is checked against the hash recorded for that run.
Usage: build_bundle.py --out /mnt/shared/shared/pscorr_flexic
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
WS = Path("/home/allenjin/Projects/DAC_pscorr")
PAPER = WS / "Overleaf/DAC-2026-PSCORR/src/figures"
ROCKET_OUT = WS / "experiments/PdatProjectForrocket/PdatScorr/output"
CVA6_EVIDENCE = HERE.parent / "evidence/cva6_paper_reset_v1"
IBEX_OUT = WS / "code/PdatProject/ScorrPdat/output/comparison"
IBEX_TABLE4 = [  # (design, label, run folder, reference design or "")
    ("table4_rv32im", "RV32IM", "rv32im_20251118_144414/run_1/isa_only/depth_4/ibex_rv32im", ""),
    ("table4_rv32im_timing", "RV32IM + timing", "rv32im_20251118_144414/run_1/with_timing/depth_4/ibex_rv32im_timing", "table4_rv32im"),
    ("table4_rv32im_no_mul", "RV32IM_no_mul", "rv32im_no_mul_20251118_151312/run_1/isa_only/depth_4/ibex_rv32im_no_mul", ""),
    ("table4_rv32im_no_mul_timing", "RV32IM_no_mul + timing", "rv32im_no_mul_20251118_151312/run_1/with_timing/depth_4/ibex_rv32im_no_mul_timing", "table4_rv32im_no_mul"),
    ("table4_rv32i", "RV32I", "rv32i_20251118_144437/run_1/isa_only/depth_4/ibex_rv32i", ""),
    ("table4_rv32i_timing", "RV32I + timing", "rv32i_20251118_144437/run_1/with_timing/depth_4/ibex_rv32i_timing", "table4_rv32i"),
]
YOSYS = "/usr/bin/yosys"  # 0.33, the version that produced every recorded area


def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def paper_rows(name: str) -> list[dict]:
    with (PAPER / name).open(newline="") as f:
        return list(csv.DictReader(f))


def collect() -> list[dict]:
    rows = []
    # Rocket: 21 workloads, each normalized to its own RV32IM run (paper Fig. 4).
    summary = json.loads((WS / "docs/evidence/rocket_hardware_summary.json").read_text())
    recorded = {}
    for pair in summary["pairs"]:
        for role in ("original", "gp"):
            run = pair[role]
            recorded[run["run"]] = (run["area_um2"], run["sources"]["_post_abc.aig"]["sha256"])
    for r in paper_rows("rocket_generality.csv"):
        w = r["workload"]
        for role, suffix, ref in (("reference", "gp", ""), ("workload", "original", f"rocket/{w}__rv32im")):
            run = f"{w}_variant_{suffix}"
            area, digest = recorded[run]
            rows.append(dict(id=f"rocket/{w}" + ("__rv32im" if suffix == "gp" else ""), core="rocket",
                             study="fig4_generality", label=r["label"] + (" (RV32IM ref)" if suffix == "gp" else ""),
                             role=role, reference_id=ref, top="rocket_synth_wrapper", clock="clock",
                             src_aig=ROCKET_OUT / run / "rocket_optimized_post_abc.aig", sha256=digest,
                             src_constraints=ROCKET_OUT / run / "rocket_optimized_assumptions.sv",
                             sky130_area_um2=area, source_run=str(ROCKET_OUT / run)))
    # CVA6: 21 workloads + one RV32IM reference (paper Fig. 4); hashes from the evidence manifest.
    manifest = {}
    for line in (CVA6_EVIDENCE / "omitted_files.tsv").open():
        p, _, h = line.rstrip("\n").split("\t")
        if p.endswith("/cva6_post_abc.aig"):
            manifest[Path(p).parent.name] = (Path(p), h)
    gp_info = json.loads((CVA6_EVIDENCE / "cva6_generality.json").read_text())
    gp_dir = Path(gp_info["gp_run"]).name
    gp_aig, gp_h = manifest[gp_dir]
    rows.append(dict(id="cva6/rv32im", core="cva6", study="fig4_generality", label="RV32IM (ref)", role="reference",
                     reference_id="", top="cva6", clock="clk_i", src_aig=gp_aig, sha256=gp_h,
                     src_constraints=gp_aig.parent / "assumptions_isa.sv",
                     sky130_area_um2=float(gp_info["gp_area_um2"]), source_run=str(gp_aig.parent)))
    for r in paper_rows("cva6_generality.csv"):
        aig, h = manifest[r["workload"]]
        rows.append(dict(id=f"cva6/{r['workload']}", core="cva6", study="fig4_generality", label=r["label"],
                         role="workload", reference_id="cva6/rv32im", top="cva6", clock="clk_i", src_aig=aig, sha256=h,
                         src_constraints=aig.parent / "assumptions_isa.sv",
                         sky130_area_um2=float(r["area_um2"]), source_run=str(aig.parent)))
    # Ibex: the six runs of paper Table 4 (timing-level constraints).
    for design, label, run, ref in IBEX_TABLE4:
        d = IBEX_OUT / run
        aig = d / "ibex_optimized_post_abc.aig"
        cons = d / ("ibex_optimized_assumptions_timing.sv" if ref else "ibex_optimized_assumptions.sv")
        rows.append(dict(id=f"ibex/{design}", core="ibex", study="table4_timing", label=label,
                         role="workload" if ref else "reference", reference_id=f"ibex/{ref}" if ref else "",
                         top="ibex_core_with_rf", clock="clk_i", src_aig=aig, sha256=sha(aig),
                         src_constraints=cons, extra_constraints=(d / "ibex_optimized_assumptions.sv") if ref else None,
                         sky130_area_um2=float((d / "ibex_optimized_total_area.txt").read_text().split()[0]),
                         source_run=str(d)))
    return rows


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    out = args.out
    out.mkdir(parents=True, exist_ok=False)
    rows = collect()
    for r in rows:
        dst = out / "designs" / r["id"]
        dst.mkdir(parents=True)
        if sha(r["src_aig"]) != r["sha256"]:
            raise SystemExit(f"hash mismatch: {r['src_aig']}")
        shutil.copy2(r["src_aig"], dst / "optimized.aig")
        shutil.copy2(r["src_constraints"], dst / "constraints.sv")
        if r.get("extra_constraints"):
            shutil.copy2(r["extra_constraints"], dst / "constraints_isa.sv")
        # Technology-independent Verilog of the same netlist, for non-Yosys flows.
        subprocess.run([YOSYS, "-q", "-p", f"read_aiger -clk_name {r['clock']} {dst / 'optimized.aig'}; "
                        f"rename -top {r['top']}; write_verilog -noattr {dst / 'optimized_generic.v'}"], check=True)
    for name in ("map_area.sh", "run_all.py", "README.md"):
        shutil.copy2(HERE / name, out / name)
    (out / "map_area.sh").chmod(0o755)
    (out / "run_all.py").chmod(0o755)
    fields = ["id", "core", "study", "label", "role", "reference_id", "top", "clock",
              "sky130_area_um2", "aig_sha256", "source_run"]
    with (out / "manifest.csv").open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        for r in rows:
            w.writerow({**{k: r[k] for k in fields if k in r}, "aig_sha256": r["sha256"]})
    print(f"{len(rows)} designs -> {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
