#!/usr/bin/env python3
"""Re-run the area map of a substituted core and keep the mapped gate netlist.

The Yosys commands are those of isa_baseline/map.py, checked character for
character against the reference run's script. Two commands are appended after the
area report: the top module is renamed and the mapped netlist is written. The
reported cell area and cell counts must equal the reference run exactly, so the
written netlist is the one whose area is reported.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import shutil
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
sys.path.insert(0, str(REPO))
sys.path.insert(0, str(HERE.parent))
from odc.temporal import checked_yosys, digest, yosys_path  # noqa: E402
from prepare_frontend import workspace_root  # noqa: E402

LIBERTY = Path("/opt/pdk/skywater-pdk/libraries/sky130_fd_sc_hd/latest/timing/sky130_fd_sc_hd__tt_025C_1v80.lib")
TOP = "Mapped"


def map_script(design: Path, out: Path, liberty: Path) -> str:
    """The script of isa_baseline/map.py for this design and output directory."""
    return (f'read_json {yosys_path(design)}\nhierarchy -check -top datapath\ncheck -assert\n'
            'select -assert-none t:$assume t:$assert t:$cover t:$check t:$anyseq t:$anyconst\nselect *\n'
            'bwmuxmap\nbmuxmap\ndemuxmap\nmemory_map\nsynth -top datapath\n'
            f'dfflibmap -liberty {yosys_path(liberty)}\nabc -liberty {yosys_path(liberty)}\nclean\n'
            f'tee -o {yosys_path(out / "stat.json")} stat -json -liberty {yosys_path(liberty)}\n')


def main() -> int:
    workspace = workspace_root(HERE)
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--substitute", type=Path, required=True, help="substitute.py output directory")
    ap.add_argument("--reference", type=Path, required=True, help="isa_baseline/map.py run on the same design")
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--liberty", type=Path, default=LIBERTY)
    ap.add_argument("--yosys", default=str(workspace / "tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys"))
    ap.add_argument("--timeout", type=int, default=3600)
    args = ap.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    shutil.copyfile(Path(__file__), out / "map_netlist.py")
    sdir, ref = args.substitute.resolve(), args.reference.resolve()
    ssum = json.loads((sdir / "summary.json").read_text())
    design = sdir / "design.json"
    if ssum.get("status") != "substituted" or digest(design) != ssum["output_design_sha256"]:
        raise ValueError(f"{sdir} is not a valid substitution record")
    rsum = json.loads((ref / "summary.json").read_text())
    if rsum.get("status") != "mapped" or rsum["design_sha256"] != ssum["output_design_sha256"] \
            or rsum["liberty_sha256"] != digest(args.liberty):
        raise ValueError("Reference map run is not a map of this design with this liberty")
    if (ref / "map.ys").read_text() != map_script(design, ref, args.liberty):
        raise ValueError("Reference map script differs from the reproduced commands")
    script = map_script(design, out, args.liberty) + f"rename datapath {TOP}\nwrite_verilog -noattr {yosys_path(out / 'mapped.v')}\n"
    record = {"status": "running", "substitute": str(sdir), "substitute_summary_sha256": digest(sdir / "summary.json"),
              "design_sha256": ssum["output_design_sha256"], "constant_sources": ssum["constant_sources"],
              "reference": str(ref), "reference_summary_sha256": digest(ref / "summary.json"),
              "liberty": str(args.liberty), "liberty_sha256": digest(args.liberty), "top": TOP,
              "script_sha256": digest(Path(__file__))}
    (out / "summary.json").write_text(json.dumps(record, indent=2) + "\n")
    record["execution"] = checked_yosys(args.yosys, script, out, "map", args.timeout)
    stats = json.loads((out / "stat.json").read_text())["modules"]["\\datapath"]
    if any(name.startswith("$") for name in stats["num_cells_by_type"]):
        raise ValueError("Unmapped cells remain")
    reproduced = stats["area"] == rsum["cell_area"] and stats["num_cells"] == rsum["cells"] \
        and stats["num_cells_by_type"] == rsum["cell_types"]
    if digest(design) != record["design_sha256"]:
        raise ValueError("Design changed during mapping")
    record.update(status="mapped" if reproduced else "differs_from_reference", cell_area=stats["area"],
                  cells=stats["num_cells"], cell_types=stats["num_cells_by_type"],
                  netlist_sha256=digest(out / "mapped.v"))
    (out / "summary.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({k: record[k] for k in ("status", "cell_area", "cells", "netlist_sha256")}))
    return 0 if reproduced else 1


if __name__ == "__main__":
    raise SystemExit(main())
