#!/usr/bin/env python3
"""Measure the fixed, qualified whole core before selecting a storage target.

This maps the unmodified baseline only. It is not an optimization or a size sweep.
"""
import argparse
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[2]))
from odc.temporal import checked_yosys, digest, yosys_path
from prepare_frontend import PRE_FPU_PIN, workspace_root


def main():
    workspace = workspace_root(HERE)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--frontend", type=Path, default=workspace / "experiments/bounded_dynamic/len5/build/pre_fpu_frontend")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--yosys", default=str(workspace / "tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys"))
    parser.add_argument("--liberty", type=Path, default=Path("/opt/pdk/skywater-pdk/libraries/sky130_fd_sc_hd/latest/timing/sky130_fd_sc_hd__tt_025C_1v80.lib"))
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args()
    source = args.frontend.resolve()
    manifest = json.loads((source / "manifest.json").read_text())
    assert manifest["upstream_commit"] == PRE_FPU_PIN
    assert manifest["status"] == "normalized_structural_check_passed"
    assert manifest["original_sha256"] == manifest["prepared_sha256"]
    assert digest(source / "normalized.il") == manifest["normalized_il_sha256"]
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    record = {"status": "running", "scope": "Unmodified whole-core library-mapped baseline; no optimization or layout/timing claim",
              "frontend_manifest_sha256": digest(source / "manifest.json"),
              "normalized_il_sha256": digest(source / "normalized.il"),
              "liberty_sha256": digest(args.liberty), "source_commit": PRE_FPU_PIN,
              "capacities": manifest["capacity_parameters_unchanged"]}
    (out / "summary.json").write_text(json.dumps(record, indent=2) + "\n")
    try:
        record["execution"] = checked_yosys(args.yosys,
            f"read_rtlil {yosys_path(source / 'normalized.il')}\n"
            "hierarchy -check -top datapath\ncheck -assert\n"
            "select -assert-none t:$assume t:$assert t:$check\nselect *\n"
            "bwmuxmap\nbmuxmap\ndemuxmap\nmemory_map\nsynth -top datapath\n"
            f"dfflibmap -liberty {yosys_path(args.liberty)}\n"
            f"abc -liberty {yosys_path(args.liberty)}\nclean\n"
            f"tee -o {yosys_path(out / 'stat.json')} stat -json -liberty {yosys_path(args.liberty)}\n",
            out, "map", args.timeout)
        stats = json.loads((out / "stat.json").read_text())["modules"]["\\datapath"]
        assert not any(kind.startswith("$") for kind in stats["num_cells_by_type"])
        record.update(status="mapped", cell_area=stats["area"], cells=stats["num_cells"],
                      cell_types=stats["num_cells_by_type"])
    except Exception as error:
        record.update(status="failed", error=str(error))
    (out / "summary.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({key: value for key, value in record.items() if key != "cell_types"}, indent=2))
    if record["status"] != "mapped":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
