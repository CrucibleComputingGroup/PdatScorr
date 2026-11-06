#!/usr/bin/env python3
"""Mechanism test with CRISP-generated wait-time monitors and reset-first semantics.

For each response-latency bound: CRISP (ldq_lat<N>.dsl, ldq_crisp.yaml) -> SVA via the
extended generator -> scripts/inject_checker.py into ldq_top.sv together with the
reset-first assumption -> stock Yosys commands -> ABC `scorr -c -m -F k` without
`cycle 100`, constraints removed as in synth_core.sh -> latch count after cleanup.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
sys.path.insert(0, str(REPO / "scripts"))
sys.path.insert(0, str(HERE.parent / "len5"))
from make_synthesis_script import _generate_synthesis_commands  # noqa: E402
from run_len5 import CRISP_DEFAULT, RESET_FIRST, YOSYS_SLANG  # noqa: E402


def stats(text):
    pat = r"i/o =\s*(\d+)/\s*(\d+)(?:\s*\(c=(\d+)\))?\s+lat =\s*(\d+)\s+and =\s*(\d+)"
    return [{"pi": int(a), "po": int(b), "c": int(c or 0), "lat": int(d), "and": int(e)}
            for a, b, c, d, e in re.findall(pat, text)]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--lats", nargs="+", type=int, default=[1, 2, 3, 4])
    ap.add_argument("--depths", nargs="+", type=int, default=[1, 4])
    ap.add_argument("--frontend", choices=("synlig", "slang"), default="synlig")
    ap.add_argument("--crisp", type=Path, default=CRISP_DEFAULT)
    args = ap.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ, PYTHONPATH=str(args.crisp))
    rows = []
    for lat in args.lats:
        d = out / f"lat{lat}"
        d.mkdir()
        dsl = HERE / f"ldq_lat{lat}.dsl"
        subprocess.run([sys.executable, "-m", "pdat_dsl", "codegen", "--config", str(HERE / "ldq_crisp.yaml"),
                        str(dsl), str(d / "isa.sv")], env=env, check=True, capture_output=True)
        (d / "assume.sv").write_text((d / "isa_timing.sv").read_text() + RESET_FIRST)
        subprocess.run([sys.executable, str(REPO / "scripts/inject_checker.py"), "--assumptions-file",
                        str(d / "assume.sv"), str(HERE / "ldq_top.sv"), str(d / "ldq_top.sv")],
                       check=True, capture_output=True)
        read = (f"read_systemverilog {HERE/'ldq.sv'} {d/'ldq_top.sv'}" if args.frontend == "synlig"
                else f"read_slang --top ldq_top {HERE/'ldq.sv'} {d/'ldq_top.sv'}")
        (d / "synth.ys").write_text(read + "\n" + _generate_synthesis_commands("ldq_top", str(d / "ldq")))
        tool = ["synlig"] if args.frontend == "synlig" else [str(YOSYS_SLANG), "-m", "slang"]
        subprocess.run(tool + ["-q", "-s", "synth.ys"], cwd=d, check=True, capture_output=True)
        aig = d / "ldq_yosys.aig"
        pre = stats(subprocess.run(["abc", "-c", f"read_aiger {aig}; print_stats"], capture_output=True, text=True).stdout)[0]
        real = pre["po"] - pre["c"]
        rm = "".join(f" removepo -N {i};" for i in range(pre["po"] - 1, real - 1, -1))
        for k in args.depths:
            cmd = (f"read_aiger {aig}; strash; scorr -c -m -F {k} -C 30000 -S 20; constr -r;{rm}"
                   " rewrite -l; balance -l; scleanup; print_stats")
            post = stats(subprocess.run(["abc", "-c", cmd], capture_output=True, text=True).stdout)[-1]
            rows.append({"lat": lat, "depth": k, "frontend": args.frontend, "before": pre, "after": post, "abc_command": cmd})
            print(json.dumps({"lat": lat, "depth": k, "latches_before": pre["lat"], "latches_after": post["lat"]}))
    (out / "summary.json").write_text(json.dumps(rows, indent=2) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
