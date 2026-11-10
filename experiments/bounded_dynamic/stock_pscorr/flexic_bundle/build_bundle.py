#!/usr/bin/env python3
"""Assemble the FlexIC area bundle: the paper's Pscorr-optimized netlists for
Rocket, CVA6 and Ibex, a technology-mapping script that takes any Liberty file,
and a manifest with the recorded SKY130 areas.

Each design is copied from the archived run that produced the paper's number,
and its AIG is checked against the hash recorded for that run. The Ibex Fig. 3
designs come from regenerated runs (ibex_fig3/README.md); each is checked against
the AND count and SKY130 area recorded for the paper's figure; two of the 13 differ
slightly and are listed in IBEX_FIG3_DEVIATIONS.

Usage: build_bundle.py --out /mnt/shared/shared/pscorr_flexic            (new bundle)
       build_bundle.py --out /mnt/shared/shared/pscorr_flexic --update   (add missing designs)
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
IBEX_FIG3_OUT = WS / "experiments/ibex_fig3_regen/final"  # written by ibex_fig3/regenerate.sh
STD = "ibex_optimized"  # netlist prefix of a plain run
ODC = "odc_optimized_synthesis/ibex_register_file_ff_optimized"  # after the register-file ODC optimization
IBEX_FIG3 = [  # (design, study, label, reference design or "", run folder, netlist prefix, paper AND gates, paper area)
    ("fig3_regs_32", "fig3_registers", "32 regs", "", "reg_count_odc/32regs", STD, 17971, 89873.7),
    ("fig3_regs_16", "fig3_registers", "16 regs", "fig3_regs_32", "reg_count_odc/16regs", ODC, 13279, 65470.3),
    ("fig3_regs_08", "fig3_registers", "8 regs", "fig3_regs_32", "reg_count_odc/08regs", ODC, 10931, 53528.8),
    ("fig3_regs_04", "fig3_registers", "4 regs", "fig3_regs_32", "reg_count_odc/04regs", ODC, 9774, 47314.1),
    ("fig3_isa_rv32im", "fig3_isa", "RV32IM", "", "isa_subsets/01_full_rv32im", STD, 24289, 126176.0),
    ("fig3_isa_rv32i", "fig3_isa", "RV32I", "fig3_isa_rv32im", "isa_subsets/02_rv32i_only", STD, 17971, 89873.7),
    ("fig3_isa_no_shifts", "fig3_isa", "No Shifts", "fig3_isa_rv32im", "isa_subsets/03_no_shifts", STD, 17270, 87447.6),
    ("fig3_isa_no_branches", "fig3_isa", "No Branches", "fig3_isa_rv32im", "isa_subsets/04_no_branches", STD, 17948, 89643.5),
    ("fig3_isa_arith_only", "fig3_isa", "Arith Only", "fig3_isa_rv32im", "isa_subsets/05_arith_only", STD, 15979, 82400.3),
    ("fig3_width_32", "fig3_width", "32-bit", "", "data_width/writeconcat/width32", STD, 17946, 89851.2),
    ("fig3_width_24", "fig3_width", "24-bit", "fig3_width_32", "data_width/writeconcat/width24", STD, 15257, 75737.6),
    ("fig3_width_16", "fig3_width", "16-bit", "fig3_width_32", "data_width/writeconcat/width16", STD, 12490, 61993.2),
    ("fig3_width_08", "fig3_width", "8-bit", "fig3_width_32", "data_width/writeconcat/width08", STD, 9545, 47125.2),
]
# Regenerated designs that do not reproduce the paper's record exactly: design -> (AND gates, area)
# of the regenerated netlist. Both are stable over repeated runs (ibex_fig3/README.md).
IBEX_FIG3_DEVIATIONS = {
    "fig3_regs_08": (10930, 53531.3),  # paper: 10931 AND gates, 53528.8 um2
    "fig3_regs_04": (9774, 47324.1),   # paper: 9774 AND gates, 47314.1 um2
}
YOSYS = "/usr/bin/yosys"  # 0.33, the version that produced every recorded area


def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def paper_rows(name: str) -> list[dict]:
    with (PAPER / name).open(newline="") as f:
        return list(csv.DictReader(f))


def collect_paper() -> list[dict]:
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


def collect_fig3() -> list[dict]:
    """Ibex: the 13 configurations of paper Fig. 3, from the regenerated runs.

    The original netlists were not preserved, so a regenerated netlist is accepted only
    if its AND count and SKY130 area equal the values recorded for the paper's figure,
    or the documented values of IBEX_FIG3_DEVIATIONS.
    """
    rows = []
    for design, study, label, ref, run, prefix, paper_ands, paper_area in IBEX_FIG3:
        d = IBEX_FIG3_OUT / run
        aig = d / f"{prefix}_post_abc.aig"
        area = float((d / f"{prefix}_total_area.txt").read_text().split()[0])
        with aig.open("rb") as f:
            ands = int(f.readline().split()[5])  # AIGER header: aig M I L O A
        want_ands, want_area = IBEX_FIG3_DEVIATIONS.get(design, (paper_ands, paper_area))
        if ands != want_ands or abs(area - want_area) > 0.05:
            raise SystemExit(f"{design}: regenerated {ands} ANDs, {area} um2; expected {want_ands} ANDs, {want_area} um2")
        # Present only where the netlist was synthesized with a replacement register file.
        regfile = d / "odc_optimized_rtl/ibex_register_file_ff_optimized.sv"
        rows.append(dict(id=f"ibex/{design}", core="ibex", study=study, label=label,
                         role="workload" if ref else "reference", reference_id=f"ibex/{ref}" if ref else "",
                         top="ibex_core_with_rf", clock="clk_i", src_aig=aig, sha256=sha(aig),
                         src_constraints=d / f"{prefix}_assumptions.sv",
                         register_file=regfile if regfile.exists() else None,
                         sky130_area_um2=area, source_run=str(d)))
    return rows


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--update", action="store_true",
                    help="add the designs missing from an existing bundle; existing designs and manifest rows are kept")
    args = ap.parse_args()
    out = args.out
    fields = ["id", "core", "study", "label", "role", "reference_id", "top", "clock",
              "sky130_area_um2", "aig_sha256", "source_run"]
    if args.update:
        with (out / "manifest.csv").open(newline="") as f:
            kept = list(csv.DictReader(f))
        have = {r["id"] for r in kept}
        rows = [r for r in collect_fig3() if r["id"] not in have]
    else:
        out.mkdir(parents=True, exist_ok=False)
        kept = []
        rows = collect_paper() + collect_fig3()
    for r in rows:
        dst = out / "designs" / r["id"]
        dst.mkdir(parents=True)
        if sha(r["src_aig"]) != r["sha256"]:
            raise SystemExit(f"hash mismatch: {r['src_aig']}")
        shutil.copy2(r["src_aig"], dst / "optimized.aig")
        shutil.copy2(r["src_constraints"], dst / "constraints.sv")
        if r.get("extra_constraints"):
            shutil.copy2(r["extra_constraints"], dst / "constraints_isa.sv")
        if r.get("register_file"):
            shutil.copy2(r["register_file"], dst / "register_file.sv")
        # Technology-independent Verilog of the same netlist, for non-Yosys flows.
        subprocess.run([YOSYS, "-q", "-p", f"read_aiger -clk_name {r['clock']} {dst / 'optimized.aig'}; "
                        f"rename -top {r['top']}; write_verilog -noattr {dst / 'optimized_generic.v'}"], check=True)
    for name in ("map_area.sh", "run_all.py", "README.md"):
        shutil.copy2(HERE / name, out / name)
    (out / "map_area.sh").chmod(0o755)
    (out / "run_all.py").chmod(0o755)
    with (out / "manifest.csv").open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        w.writerows(kept)
        for r in rows:
            w.writerow({**{k: r[k] for k in fields if k in r}, "aig_sha256": r["sha256"]})
    print(f"{len(rows)} designs added, {len(kept) + len(rows)} in total -> {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
