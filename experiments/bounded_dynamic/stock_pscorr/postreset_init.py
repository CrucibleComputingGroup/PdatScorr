#!/usr/bin/env python3
"""Give a design the initial state reached after a reset sequence, with assumptions kept.

Yosys `sim` cannot evaluate formal cells ($check/$assume), so the reset sequence is
simulated on a copy without them, and the resulting register values are carried back
by wire name:

1. <design.il> is the elaborated design (after the stock proc/opt/memory/techmap/opt).
2. A copy has its formal cells removed (`chformal -remove`); `sim` applies the reset for
   N cycles starting from all-X state and writes the final state back (`-w`) as `init`
   attributes. Registers that reset hold their reset values; registers without a reset
   stay X, i.e. keep no init attribute and later receive arbitrary initial values from
   `write_aiger -zinit`.
3. The `init` attributes are copied, by wire name, into <design.il>, which keeps its
   assumptions.

Usage: postreset_init.py <yosys> <design.il> <out.il> --clock C --reset R [--active-low] [--cycles N]
"""
from __future__ import annotations

import argparse
import re
import subprocess
from pathlib import Path


def wire_inits(il: str) -> dict:
    inits, pending = {}, None
    for line in il.splitlines():
        s = line.strip()
        m = re.match(r"attribute \\init (\S+)$", s)
        if m:
            pending = m.group(1)
            continue
        if s.startswith("attribute "):
            continue
        m = re.match(r"wire\b.* (\S+)$", s)
        if m and pending is not None:
            if "1" in pending.split("'")[-1] or "0" in pending.split("'")[-1]:
                inits[m.group(1)] = pending
        pending = None
    return inits


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("yosys")
    ap.add_argument("design", type=Path)
    ap.add_argument("out", type=Path)
    ap.add_argument("--clock", required=True)
    ap.add_argument("--reset", required=True)
    ap.add_argument("--active-low", action="store_true")
    ap.add_argument("--cycles", type=int, default=16)
    args = ap.parse_args()
    sim_il = args.out.with_suffix(".sim.il")
    rst = f"-resetn {args.reset}" if args.active_low else f"-reset {args.reset}"
    script = (f"read_rtlil {args.design}\nchformal -remove\n"
              f"sim -clock {args.clock} {rst} -rstlen {args.cycles} -n {args.cycles} -w -q\n"
              f"write_rtlil {sim_il}\n")
    subprocess.run([args.yosys, "-q", "-p", script], check=True)
    inits = wire_inits(sim_il.read_text())
    out, applied = [], 0
    pending_init = False
    for line in args.design.read_text().splitlines():
        s = line.strip()
        if re.match(r"attribute \\init ", s):
            pending_init = True
        m = re.match(r"(\s*)wire\b.* (\S+)$", line)
        if m and m.group(2) in inits and not pending_init:
            out.append(f"{m.group(1)}attribute \\init {inits[m.group(2)]}")
            applied += 1
        if not s.startswith("attribute "):
            pending_init = False
        out.append(line)
    args.out.write_text("\n".join(out) + "\n")
    print(f"{applied} wires given post-reset initial values ({len(inits)} initialized in simulation)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
