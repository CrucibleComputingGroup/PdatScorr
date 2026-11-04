#!/usr/bin/env python3
"""Normalize and physically map a prepared Core in one modern Yosys process.

This is a separately matched flow family.  It avoids Verilog reread/export and
never invokes AIGER zinit.  The mapper still uses the explicit legacy fast ABC
sequence and the same system yosys-abc binary and SKY130 HD Liberty.
"""
import argparse
import hashlib
import json
import re
import subprocess
import time
from pathlib import Path


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    root = Path(__file__).resolve().parents[3]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("prepared", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--yosys", type=Path, default=root / "tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys")
    parser.add_argument("--abc", type=Path, default=Path("/usr/bin/yosys-abc"))
    parser.add_argument("--liberty", type=Path, default=Path("/opt/pdk/skywater-pdk/libraries/sky130_fd_sc_hd/latest/timing/sky130_fd_sc_hd__tt_025C_1v80.lib"))
    parser.add_argument("--timeout", type=int, default=7200)
    parser.add_argument("--write-netlist", action="store_true", help="Optional potentially expensive Verilog export, after area statistics")
    args = parser.parse_args()
    source, output = args.prepared.resolve(), args.output.resolve()
    source_manifest = json.loads((source / "manifest.json").read_text())
    for relative, expected in source_manifest["source_files"].items():
        if sha(source / "src" / relative) != expected:
            raise SystemExit(f"Prepared source changed: {relative}")
    if output.exists():
        raise SystemExit(f"Refusing existing output directory: {output}")
    output.mkdir(parents=True)
    input_script = source / "synth.ys"
    # Keep the exact prepared frontend and inherited normalization.  Both
    # serialization exports are removed; no reparse or zinit occurs.
    normalization = "\n".join(line for line in input_script.read_text().splitlines()
                               if not re.match(r"\s*write_(?:aiger|verilog)\b", line)) + "\n"
    assert not re.search(r"^\s*write_aiger\b", normalization, re.M)
    abc_script = output / "legacy_fast.abc"
    abc_script.write_text("strash\ndretime\nmap\n")
    liberty = args.liberty.resolve()
    mapping = f"""
# Physical hardware only: remove any proof-only assumptions.
chformal -assume -remove
opt_clean
dfflibmap -liberty {liberty}
abc -exe {args.abc.resolve()} -liberty {liberty} -script {abc_script} -nocleanup
opt_clean
tee -o {output / 'area.json'} stat -json -liberty {liberty}
stat -liberty {liberty}
"""
    if args.write_netlist:
        mapping += f"write_verilog -noattr -noexpr {output / 'gates.v'}\n"
    script = output / "map.ys"
    script.write_text(normalization + mapping)
    command = [str(args.yosys.resolve()), "-m", "slang", "-Q", "-T", "-s", str(script)]
    manifest = {
        "status": "running", "flow_family": "modern_inprocess_physical",
        "scope": "Whole RSD Core including flop-mapped cache/register memories; no SRAM macros, SoC peripherals, placement or routing",
        "initialization": "Original normalized RTL state; no AIGER zinit conversion",
        "source_manifest": str(source / "manifest.json"), "source_manifest_sha256": sha(source / "manifest.json"),
        "source_script_sha256": sha(input_script), "source_files": source_manifest["source_files"],
        "defines": source_manifest["defines"], "configuration": source_manifest["configuration"],
        "abc_script": abc_script.read_text(), "abc_path": str(args.abc.resolve()), "abc_sha256": sha(args.abc.resolve()),
        "library": str(liberty), "library_sha256": sha(liberty),
        "command": command, "map_script_sha256": sha(script), "optional_verilog_export": args.write_netlist,
        "comparison_rule": "Compare only within this matched flow family; do not mix its denominator with legacy reread maps or AIGER formal models",
    }
    result = output / "manifest.json"
    result.write_text(json.dumps(manifest, indent=2) + "\n")
    started = time.monotonic()
    try:
        with (output / "mapping.log").open("w") as log:
            completed = subprocess.run(command, cwd=output, stdout=log, stderr=subprocess.STDOUT, timeout=args.timeout)
        manifest["returncode"] = completed.returncode
        if completed.returncode:
            raise RuntimeError("In-process mapping failed; see mapping.log")
        areas = re.findall(r"Chip area for (?:top )?module[^:]*:\s*([\d.]+)", (output / "mapping.log").read_text())
        if not areas or not (output / "area.json").exists():
            raise RuntimeError("No final mapped area/statistics")
        data = json.loads((output / "area.json").read_text())
        if not sum(module["num_cells"] for module in data["modules"].values()):
            raise RuntimeError("Unexpected empty full core")
        manifest.update(status="complete", cell_area_um2=float(areas[-1]))
    except BaseException as error:
        manifest.update(status="failed", error=str(error))
        raise
    finally:
        manifest["elapsed_seconds"] = time.monotonic() - started
        result.write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps({key: manifest[key] for key in ["status", "cell_area_um2", "elapsed_seconds"]}, indent=2))


if __name__ == "__main__":
    main()
