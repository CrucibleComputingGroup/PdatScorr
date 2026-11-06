#!/usr/bin/env python3
"""Rerun one of the paper's Rocket workload runs, with the stock or the reset flow.

Inputs come from the paper's own run directory (experiment checkout
PdatProjectForrocket/PdatScorr/output/<workload>_variant_<original|gp>): the Rocket core
source with the CRISP ISA assumptions already injected (rocket_optimized_id_stage.sv)
and the Synlig script (rocket_optimized_synth.ys). Both are reused unchanged except
for file locations, so the ISA constraint is the paper's byte for byte.

--flow stock  reproduces the paper's command: ABC `cycle 100; scorr -c -m -F 5 ...`.
--flow reset  adds the reset-first assumption to the wrapper (reset is active high in
              Rocket) and drops `cycle 100`, so scorr's base case starts from reset and
              registers without a reset keep arbitrary initial values.
Mapping uses the same scripts/synth_to_gates.sh as the paper.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

WS = Path("/home/allenjin/Projects/DAC_pscorr/experiments/PdatProjectForrocket")
OLD = "/home/allenjin/Codes/ISCA_rebuttal/PdatProjectForrocket"
PAPER_RUNS = WS / "PdatScorr/output"
WRAPPER = WS / "PdatScorr/rocket_synth_wrapper.sv"
GATES = WS / "PdatScorr/scripts/synth_to_gates.sh"
RESET_FIRST = """
  // Pscorr reset semantics: reset is applied in the first cycle and is free afterwards
  logic pscorr_first_cycle_q = 1'b1;
  always_ff @(posedge clock) pscorr_first_cycle_q <= 1'b0;
  always_comb if (pscorr_first_cycle_q) assume (reset);
"""


def sha(p: Path) -> str:
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def stats(text: str):
    pat = r"i/o =\s*(\d+)/\s*(\d+)(?:\s*\(c=(\d+)\))?\s+lat =\s*(\d+)\s+and =\s*(\d+)"
    return [{"pi": int(a), "po": int(b), "c": int(c or 0), "lat": int(d), "and": int(e)}
            for a, b, c, d, e in re.findall(pat, text)]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--paper-run", required=True, help="e.g. libstatemate_variant_original")
    ap.add_argument("--flow", choices=("stock", "reset"), required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    src = PAPER_RUNS / args.paper_run
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    core = out / "rocket_core_injected.sv"
    shutil.copyfile(src / "rocket_optimized_id_stage.sv", core)
    wrapper = out / "rocket_synth_wrapper.sv"
    if args.flow == "reset":
        (out / "reset_first.sv").write_text(RESET_FIRST)
        subprocess.run([sys.executable, str(Path(__file__).resolve().parents[4] / "scripts/inject_checker.py"),
                        "--assumptions-file", str(out / "reset_first.sv"), str(WRAPPER), str(wrapper)],
                       check=True, stdout=subprocess.DEVNULL)
    else:
        shutil.copyfile(WRAPPER, wrapper)
    ys = (src / "rocket_optimized_synth.ys").read_text()
    ys = ys.replace(f"{OLD}/PdatScorr/output/{args.paper_run}/rocket_optimized_id_stage.sv", str(core))
    ys = ys.replace(f"{OLD}/PdatScorr/rocket_synth_wrapper.sv", str(wrapper))
    ys = re.sub(r"write_aiger -zinit \S+", f"write_aiger -zinit {out/'rocket_yosys.aig'}", ys)
    ys = ys.replace(OLD, str(WS))
    assert OLD not in ys
    (out / "synth.ys").write_text(ys)
    t0 = time.time()
    y = subprocess.run(["synlig", "-s", "synth.ys"], cwd=out, capture_output=True, text=True)
    (out / "yosys.log").write_text(y.stdout + y.stderr)
    if y.returncode:
        raise SystemExit(f"synlig failed: {out/'yosys.log'}")
    aig = out / "rocket_yosys.aig"
    pre = stats(subprocess.run(["abc", "-c", f"read_aiger {aig}; print_stats"], capture_output=True, text=True).stdout)[0]
    real = pre["po"] - pre["c"]
    rm = "".join(f" removepo -N {i};" for i in range(pre["po"] - 1, real - 1, -1))
    cycle = " cycle 100;" if args.flow == "stock" else ""
    cmd = (f"read_aiger {aig}; strash;{cycle} scorr -c -m -F 5 -C 30000 -S 20 -v;"
           + (f" constr -r;{rm}" if pre["c"] else "")
           + f" rewrite -l; balance -l; print_stats; write_aiger {out/'rocket_post_abc.aig'}")
    a = subprocess.run(["abc", "-c", cmd], capture_output=True, text=True)
    (out / "abc.log").write_text(a.stdout + a.stderr)
    tot = re.findall(r"^TOTAL\s*=\s*([0-9.]+) sec", a.stdout, re.M)
    g = subprocess.run(["bash", str(GATES), str(out / "rocket"), "", "clock", "rocket_synth_wrapper"],
                       cwd=out, capture_output=True, text=True)
    (out / "gates_run.log").write_text(g.stdout + g.stderr)
    area = re.findall(r"Chip area for (?:top )?module '[^']*':\s*([0-9.]+)", g.stdout)
    rec = {"paper_run": str(src), "flow": args.flow, "depth": 5, "abc_command": cmd,
           "core_injected_sha256": sha(core), "wrapper_sha256": sha(wrapper), "script_sha256": sha(Path(__file__)),
           "yosys_aig": pre, "post_abc": stats(a.stdout)[-1] if stats(a.stdout) else None,
           "scorr_seconds": float(tot[-1]) if tot else None, "cell_area": float(area[-1]) if area else None,
           "paper_area": float((src / "rocket_optimized_total_area.txt").read_text().split()[0]),
           "status": "ok" if area else "failed", "wall_seconds": round(time.time() - t0, 1)}
    (out / "summary.json").write_text(json.dumps(rec, indent=2) + "\n")
    print(json.dumps({k: rec[k] for k in ("status", "flow", "cell_area", "paper_area", "scorr_seconds")}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
