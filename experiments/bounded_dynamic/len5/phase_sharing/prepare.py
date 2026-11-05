#!/usr/bin/env python3
"""Elaborate unchanged, pinned LEN5 units and expose enabled FF banks."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
sys.path.insert(0, str(REPO))
from odc.temporal import checked_yosys, digest, yosys_path

PIN = "14291dcc5bef181085d001c5a29e7f4fc4cbc8e9"

def main():
    workspace = next(p for p in HERE.parents if (p / "tools/oss-cad-suite-20261104").exists())
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--raw-cdb", action="store_true")
    p.add_argument("--boundary", choices=("alu_cdb_rob", "alu_cdb"), default="alu_cdb_rob")
    p.add_argument("--yosys", default=str(workspace / "tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys"))
    p.add_argument("--deps", type=Path, default=workspace / "experiments/bounded_dynamic/deps/len5")
    p.add_argument("--source-list", type=Path, default=HERE.parent / "results/pre_fpu_frontend/sources.txt")
    args = p.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True)
    source = out / "source"
    files = [x.removeprefix("source/") for x in args.source_list.read_text().splitlines()]
    hashes = {}
    for name in [*files, "LICENSE"]:
        data = subprocess.check_output(["git", "-C", str(args.deps), "show", f"{PIN}:{name}"])
        dest = source / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(data)
        hashes[name] = hashlib.sha256(data).hexdigest()
    wrapper = out / "AluObserved.sv"
    wrapper_source = HERE / ("AluObserved.sv" if args.boundary == "alu_cdb_rob" else "AluCdbObserved.sv")
    wrapper.write_bytes(wrapper_source.read_bytes())
    if args.raw_cdb:
        wrapper.write_text(wrapper.read_text().replace("parameter bit RAW_CDB = 1'b0", "parameter bit RAW_CDB = 1'b1"))
    script = "plugin -i slang\nread_slang --single-unit --no-implicit-memories --top AluObserved -D SYNTHESIS "
    paths = [source / f for f in files] + [wrapper]
    if any(any(c.isspace() or c in '\";\\\\' for c in str(path)) for path in paths):
        raise ValueError("read_slang requires simple source paths")
    script += " ".join(map(str, paths)) + "\n"
    script += "hierarchy -check -top AluObserved\nflatten\nproc\nopt -keepdc\nopt_dff\nopt_clean\ncheck -assert\n"
    script += f"write_json {yosys_path(out / 'baseline.json')}\nwrite_verilog {yosys_path(out / 'baseline.v')}\nstat\n"
    result = checked_yosys(args.yosys, script, out, "prepare", 120)
    design = json.loads((out / "baseline.json").read_text())["modules"]["AluObserved"]
    seq = {n: c for n, c in design["cells"].items() if "dff" in c["type"].lower()}
    manifest = {"source_commit": PIN, "source_sha256": hashes, "wrapper_sha256": digest(wrapper),
                "raw_cdb": args.raw_cdb, "boundary": args.boundary, "top": "AluObserved",
                "capacities": {"ALU_RS": 8, **({"ROB": 32} if args.boundary == "alu_cdb_rob" else {})},
                "source_edits": [], "prepare": result, "baseline_json_sha256": digest(out / "baseline.json"),
                "baseline_verilog_sha256": digest(out / "baseline.v"),
                "ff_bits": sum(len(c["connections"]["Q"]) for c in seq.values()),
                "ff_types": {t: sum(c["type"] == t for c in seq.values()) for t in sorted({c["type"] for c in seq.values()})},
                "ports": {n: {"direction": v["direction"], "bits": len(v["bits"])} for n, v in design["ports"].items()}}
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps({"path": str(out), "ff_bits": manifest["ff_bits"], "ff_types": manifest["ff_types"]}))

if __name__ == "__main__":
    main()
