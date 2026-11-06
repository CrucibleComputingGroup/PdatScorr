#!/usr/bin/env python3
"""Run the stock Pscorr back end (Synlig -> AIGER with assumptions -> ABC scorr) on ldq_top.

For every interface-assumption variant and induction depth, record the latch and AND
counts before and after the stock ABC command, with constraints removed afterwards
exactly as synth_core.sh does. A final `scleanup` only counts what synthesis would keep.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[3] / "scripts"))
from make_synthesis_script import _generate_synthesis_commands  # noqa: E402  (stock commands)


def stats(text: str) -> dict:
    m = re.findall(r"i/o =\s*(\d+)/\s*(\d+)(?:\s*\(c=(\d+)\))?\s+lat =\s*(\d+)\s+and =\s*(\d+)", text)
    return [{"pi": int(a), "po": int(b), "c": int(c or 0), "lat": int(d), "and": int(e)} for a, b, c, d, e in m]


def run(variant: str, depth: int, params: dict, out: Path, synlig: str, abc: str) -> dict:
    out.mkdir(parents=True, exist_ok=False)
    defines = "" if variant == "none" else f"-D{variant}"
    pset = " ".join(f"-P{k}={v}" for k, v in params.items())  # Synlig elaborates at read time
    script = (f"read_systemverilog {defines} {pset} {HERE/'ldq.sv'} {HERE/'ldq_top.sv'}\n"
              + _generate_synthesis_commands("ldq_top", str(out / "ldq")))
    (out / "synth.ys").write_text(script)
    t0 = time.time()
    y = subprocess.run([synlig, "-q", "-s", "synth.ys"], cwd=out, capture_output=True, text=True)
    (out / "yosys.log").write_text(y.stdout + y.stderr)
    if y.returncode:
        return {"variant": variant, "depth": depth, "status": "yosys_failed", "log": str(out / "yosys.log")}
    aig = out / "ldq_yosys.aig"
    pre = stats(subprocess.run([abc, "-c", f"read_aiger {aig}; print_stats"], capture_output=True, text=True).stdout)[0]
    real = pre["po"] - pre["c"]
    removes = "".join(f" removepo -N {i};" for i in range(pre["po"] - 1, real - 1, -1)) if pre["c"] else ""
    cmd = (f"read_aiger {aig}; strash; cycle 100; scorr -c -m -F {depth} -C 30000 -S 20 -v;"
           + (f" constr -r;{removes}" if pre["c"] else "")
           + f" rewrite -l; balance -l; print_stats; scleanup; print_stats; write_aiger {out/'post_abc.aig'}")
    t1 = time.time()
    a = subprocess.run([abc, "-c", cmd], capture_output=True, text=True)
    (out / "abc.log").write_text(a.stdout + a.stderr)
    post = stats(a.stdout)
    return {"variant": variant, "depth": depth, "params": params, "status": "ok" if a.returncode == 0 else "abc_failed",
            "before": pre, "after_stock": post[-2] if len(post) >= 2 else None, "after_cleanup": post[-1] if post else None,
            "abc_seconds": round(time.time() - t1, 2), "yosys_seconds": round(t1 - t0, 2), "abc_command": cmd}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--variants", nargs="+", default=["none", "STALL_BOUND", "TAG_LATENCY"])
    ap.add_argument("--depths", nargs="+", type=int, default=[1, 2, 4, 8])
    ap.add_argument("--lat", type=int, default=2)
    ap.add_argument("--param", action="append", default=[], help="extra NAME=VALUE parameter of ldq_top")
    ap.add_argument("--synlig", default="synlig")
    ap.add_argument("--abc", default="abc")
    args = ap.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    rows = []
    for v in args.variants:
        for k in args.depths:
            r = run(v, k, {"LAT": args.lat, **dict(x.split("=", 1) for x in args.param)}, args.output / f"{v}_k{k}", args.synlig, args.abc)
            rows.append(r)
            print(json.dumps({x: r.get(x) for x in ("variant", "depth", "status", "before", "after_cleanup", "abc_seconds")}))
    (args.output / "summary.json").write_text(json.dumps(rows, indent=2) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
