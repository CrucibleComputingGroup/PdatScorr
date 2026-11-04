#!/usr/bin/env python3
"""Map normalized whole-core RTL before AIGER initialization encoding."""
import argparse
import hashlib
import json
import re
import subprocess
import time
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path, help="rtl_logic.v exported before write_aiger -zinit")
    parser.add_argument("output", type=Path)
    parser.add_argument("--yosys", default="/usr/bin/yosys")
    parser.add_argument("--top", default="Core")
    parser.add_argument("--scope", default="Whole RSD Core with cache/register memories mapped to flops; no SRAM macros, no SoC peripherals")
    parser.add_argument("--timeout", type=int, default=7200)
    parser.add_argument("--liberty", type=Path, default=Path("/opt/pdk/skywater-pdk/libraries/sky130_fd_sc_hd/latest/timing/sky130_fd_sc_hd__tt_025C_1v80.lib"))
    args = parser.parse_args()
    source, output, liberty = args.source.resolve(), args.output.resolve(), args.liberty.resolve()
    if output.exists():
        raise SystemExit(f"Refusing existing output directory: {output}")
    output.mkdir(parents=True)
    script = output / "map.ys"
    script.write_text(f"""read_verilog -formal {source}
chformal -assume -remove
hierarchy -check -top {args.top}
proc
flatten
opt
techmap
opt
dfflibmap -liberty {liberty}
abc -liberty {liberty} -fast
opt_clean
write_verilog -noattr -noexpr {output / 'gates.v'}
tee -o {output / 'area.json'} stat -json -liberty {liberty}
stat -liberty {liberty}
""")
    command = [args.yosys, "-Q", "-T", "-s", str(script)]
    manifest = {
        "status": "running", "source": str(source),
        "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "scope": args.scope, "top": args.top,
        "initialization": "Direct normalized RTL, no AIGER zinit encoding",
        "assumptions": "All proof-only assumptions removed before hardware mapping",
        "compatibility_patch": "This mapping stage applies no source patches; see the normalized source's manifest for frontend adaptations",
        "library": str(liberty), "command": command,
    }
    result = output / "manifest.json"
    result.write_text(json.dumps(manifest, indent=2) + "\n")
    start = time.monotonic()
    try:
        with (output / "mapping.log").open("w") as log:
            process = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, cwd=output, timeout=args.timeout)
        manifest["returncode"] = process.returncode
        if process.returncode:
            raise RuntimeError("Mapping failed; see mapping.log")
        areas = re.findall(r"Chip area for (?:top )?module[^:]*:\s*([\d.]+)", (output / "mapping.log").read_text())
        if not areas or not (output / "area.json").exists():
            raise RuntimeError("No complete mapped area output")
        manifest.update(status="complete", cell_area_um2=float(areas[-1]))
    except BaseException as error:
        manifest.update(status="failed", error=str(error))
        raise
    finally:
        manifest["elapsed_seconds"] = time.monotonic() - start
        result.write_text(json.dumps(manifest, indent=2) + "\n")
    print(result)


if __name__ == "__main__":
    main()
