#!/usr/bin/env python3
"""Program-level check of Rocket results: same programs, compare what they store.

For each model (an AIG plus the Yosys map of the AIG it was derived from, so port
indices are known), run rocketprog with the same program seed and report, per trace,
the number of stores and the hash of the store sequence. Models are compared pairwise.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
PORTS = ["reset", "io_imem_resp_valid", "io_imem_resp_bits_pc", "io_imem_resp_bits_data", "io_imem_req_valid",
         "io_imem_req_bits_pc", "io_imem_resp_ready", "io_dmem_req_ready", "io_dmem_req_valid",
         "io_dmem_req_bits_addr", "io_dmem_req_bits_tag", "io_dmem_req_bits_cmd", "io_dmem_req_bits_size",
         "io_dmem_s1_kill", "io_dmem_s1_data_data", "io_dmem_resp_valid", "io_dmem_resp_bits_tag",
         "io_dmem_resp_bits_data", "io_dmem_resp_bits_has_data", "io_dmem_resp_bits_data_word_bypass",
         "io_dmem_ordered"]


def spec_from_map(mapfile: Path, patterns: list) -> str:
    ins, outs = {}, {}
    for line in mapfile.read_text().splitlines():
        f = line.split()
        if f[0] in ("input", "output"):
            (ins if f[0] == "input" else outs).setdefault(f[3], {})[int(f[2])] = int(f[1])
    lines = [f"port {i}" for bits in ins.values() for i in bits.values()]
    for name in PORTS:
        d = ins.get(name) or outs.get(name)
        if d is None:
            raise SystemExit(f"{mapfile}: no port {name}")
        lines.append(f"vec {name} {len(d)} " + " ".join(str(d[b]) for b in sorted(d)))
    lines += [f"pattern {m} {v}" for m, v in patterns]
    return "\n".join(lines) + "\n"


def isa_patterns(sv: Path, signal: str):
    pat = re.compile(rf"\(\({re.escape(signal)} & 32'h([0-9a-f]+)\) == 32'h([0-9a-f]+)\)|"
                     rf"\(\({re.escape(signal)}\[31:0\] & 32'h([0-9a-f]+)\) == 32'h([0-9a-f]+)\)")
    out = set()
    for m in pat.finditer(sv.read_text()):
        g = [x for x in m.groups() if x]
        out.add((g[0], g[1]))
    return sorted(out)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--model", action="append", nargs=4, metavar=("NAME", "AIG", "MAP", "POWERUP_SEED"), required=True)
    ap.add_argument("--assumptions", type=Path, required=True, help="ISA assumption SV (allowed patterns)")
    ap.add_argument("--signal", default="io_imem_resp_bits_data")
    ap.add_argument("--cycles", type=int, default=20000)
    ap.add_argument("--rounds", type=int, default=4)
    ap.add_argument("--program-seed", type=int, default=1)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    out = args.output
    out.mkdir(parents=True, exist_ok=False)
    pats = isa_patterns(args.assumptions, args.signal)
    exe = out / "rocketprog"
    subprocess.run(["/usr/bin/gcc", "-O2", "-B/usr/bin/", "-o", str(exe), str(HERE / "rocketprog.c")], check=True)
    res = {}
    for name, aig, mp, seed in args.model:
        (out / f"{name}.spec").write_text(spec_from_map(Path(mp), pats))
        subprocess.run([str(exe), aig, str(out / f"{name}.spec"), str(args.cycles), str(args.rounds),
                        str(args.program_seed), seed, str(out / f"{name}.txt")], check=True)
        res[name] = [l.split() for l in (out / f"{name}.txt").read_text().splitlines()]
    names = [m[0] for m in args.model]
    base = names[0]
    report = {"patterns": len(pats), "cycles": args.cycles, "traces": len(res[base]),
              "stores_per_trace_median": sorted(int(r[2]) for r in res[base])[len(res[base]) // 2],
              "fetched_per_trace_median": sorted(int(r[4]) for r in res[base])[len(res[base]) // 2], "pairs": {}}
    for other in names[1:]:
        same = sum(1 for a, b in zip(res[base], res[other]) if a[2:4] == b[2:4])
        report["pairs"][f"{base} vs {other}"] = {"same_store_sequence": same, "of": len(res[base])}
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
