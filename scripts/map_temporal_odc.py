#!/usr/bin/env python3
"""Map a certified temporal-ODC pair without formal monitors or zinit state."""
import argparse
import json
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from odc.temporal import checked_yosys, digest, yosys_path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("analysis", type=Path)
    parser.add_argument("--liberty", type=Path, required=True)
    parser.add_argument("--yosys", default="yosys")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=float, default=120)
    args = parser.parse_args()
    analysis = args.analysis.resolve()
    report = json.loads((analysis / "report.json").read_text())
    proof = report.get("combined_proof", {})
    if report.get("status") != "proved" or proof.get("proven") is not True:
        raise SystemExit("A completed combined proof is required")
    for name, field in (("reference.v", "reference_sha256"), ("optimized.v", "candidate_sha256"),
                        ("harness.sv", "harness_sha256")):
        if digest(analysis / name) != proof.get(field):
            raise SystemExit("Certified artifact changed: " + name)
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    result = {"analysis_report_sha256": digest(analysis / "report.json"),
              "liberty_sha256": digest(args.liberty), "liberty": str(args.liberty.resolve()),
              "scope": "Hardware-only library-mapped area estimate; no proof monitors, zinit state, layout, or timing claim",
              "variants": {}}
    for name, filename in (("baseline", "reference.v"), ("optimized", "optimized.v")):
        source = analysis / filename
        text = source.read_text()
        tops = re.findall(r"(?m)^module ([A-Za-z_][A-Za-z0-9_]*)\s*\(", text)
        if len(tops) != 1:
            raise ValueError("Expected one flattened hardware module")
        top = tops[0]
        variant = out / name
        variant.mkdir()
        run = checked_yosys(args.yosys,
            f"read_verilog -sv {yosys_path(source)}\nhierarchy -check -top {top}\n"
            "select -assert-none t:$assume t:$assert t:$check\nselect *\n"
            f"synth -top {top}\n"
            f"dfflibmap -liberty {yosys_path(args.liberty)}\n"
            f"abc -liberty {yosys_path(args.liberty)}\nclean\n"
            f"write_verilog -noattr -noexpr {yosys_path(variant / 'mapped.v')}\n"
            f"tee -o {yosys_path(variant / 'stat.json')} stat -json -liberty {yosys_path(args.liberty)}\n",
            variant, "map", args.timeout)
        stats = json.loads((variant / "stat.json").read_text())
        module = stats["modules"]["\\" + top]
        kinds = module["num_cells_by_type"]
        if any(kind.startswith("$") for kind in kinds):
            raise ValueError("Physical estimate has unmapped internal cells")
        result["variants"][name] = {"source_sha256": digest(source), "execution": run,
            "cell_area": module["area"], "cells": module["num_cells"],
            "cell_types": kinds, "mapped_sha256": digest(variant / "mapped.v")}
    baseline = result["variants"]["baseline"]["cell_area"]
    optimized = result["variants"]["optimized"]["cell_area"]
    result["area_reduction_percent"] = 100 * (baseline - optimized) / baseline
    (out / "summary.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"baseline_area": baseline, "optimized_area": optimized,
                      "reduction_percent": result["area_reduction_percent"]}, indent=2))


if __name__ == "__main__":
    main()
