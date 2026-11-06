#!/usr/bin/env python3
"""Per-workload RV64IM instruction sets for LEN5, written as CRISP files.

Each Embench benchmark in the (read-only) LEN5 checkout is compiled, together with
the Embench beebs support code (not the timing harness main.c), for RV64IM (lp64, -O2, freestanding) into one relocatable
object. The canonical mnemonics in its disassembly (`-M no-aliases`) give the
instructions the workload uses. Each CRISP file includes RV64IM and forbids every
RV64IM instruction the workload does not use, the form of the Rocket workload files.
Library routines outside the benchmark and support sources are not linked, so a set
covers the compiled workload code only.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

WS = Path("/home/allenjin/Projects/DAC_pscorr")
EMBENCH = WS / "experiments/bounded_dynamic/deps/len5/sw/benchmarks/embench"
GCC, OBJDUMP = "riscv64-linux-gnu-gcc", "riscv64-linux-gnu-objdump"
FLAGS = ["-march=rv64im", "-mabi=lp64", "-O2", "-ffreestanding", "-fno-builtin", "-fno-pic",
         "-mcmodel=medany", "-DCPU_MHZ=1", "-DWARMUP_HEAT=1"]


def rv64im_names() -> list[str]:
    import sys
    sys.path.insert(0, str(WS / "code/PdatProject/PdatDslBoundedDynamic"))
    from pdat_dsl.encodings import RV32I_INSTRUCTIONS, RV32M_INSTRUCTIONS, RV64I_INSTRUCTIONS, RV64M_INSTRUCTIONS
    names = set()
    for table in (RV32I_INSTRUCTIONS, RV32M_INSTRUCTIONS, RV64I_INSTRUCTIONS, RV64M_INSTRUCTIONS):
        names.update(table)
    return sorted(names)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--build", type=Path, required=True, help="new directory for objects")
    ap.add_argument("--crisp-dir", type=Path, required=True, help="new directory for CRISP files")
    args = ap.parse_args()
    args.build.mkdir(parents=True, exist_ok=False)
    args.crisp_dir.mkdir(parents=True, exist_ok=False)
    isa = rv64im_names()
    # The Ubuntu cross toolchain ships glibc stubs only for lp64d; the stubs header just
    # marks unimplemented functions, so an empty lp64 stub changes no generated code.
    shim = args.build / "shim/gnu"
    shim.mkdir(parents=True)
    (shim / "stubs-lp64.h").write_text("")
    # main.c only times the run (CSR reads of mcycle/minstret) and calls the benchmark;
    # it is left out so each set covers the workload and its beebs support code.
    support = [EMBENCH / "support/beebsc.c"]
    records = []
    for bench in sorted(p for p in (EMBENCH / "src").iterdir() if p.is_dir()):
        srcs = sorted(bench.glob("*.c")) + support
        obj = args.build / f"{bench.name}.o"
        cmd = [GCC, *FLAGS, f"-I{args.build/'shim'}", f"-I{EMBENCH/'support'}", f"-I{bench}", "-r", "-nostdlib", "-o", str(obj), *map(str, srcs)]
        cc = subprocess.run(cmd, capture_output=True, text=True)
        if cc.returncode:
            records.append({"workload": bench.name, "status": "compile_failed", "stderr": cc.stderr[-2000:]})
            continue
        dis = subprocess.run([OBJDUMP, "-d", "-M", "no-aliases", str(obj)], capture_output=True, text=True, check=True).stdout
        used = set()
        for line in dis.splitlines():
            m = re.match(r"\s+[0-9a-f]+:\s+[0-9a-f]+\s+([a-z][a-z0-9.]*)", line)
            if m:
                used.add(m.group(1).upper())
        unknown = sorted(u for u in used if u not in isa)
        allowed = sorted(u for u in used if u in isa)
        forbidden = [n for n in isa if n not in used]
        text = ["version 2", "", f"# Embench {bench.name}, compiled for RV64IM (see make_workload_crisp.py).",
                f"# Uses {len(allowed)} RV64IM instructions: {' '.join(allowed)}",
                f"# Outside RV64IM (not constrained here): {' '.join(unknown) or 'none'}", "",
                "include RV32I", "include RV32M", "include RV64I", "include RV64M", ""]
        text += [f"forbid {n}" for n in forbidden]
        dsl = args.crisp_dir / f"{bench.name}.dsl"
        dsl.write_text("\n".join(text) + "\n")
        records.append({"workload": bench.name, "status": "ok", "sources": [str(s) for s in srcs],
                        "object_sha256": hashlib.sha256(obj.read_bytes()).hexdigest(),
                        "allowed": allowed, "outside_rv64im": unknown, "forbidden_count": len(forbidden),
                        "dsl": str(dsl), "dsl_sha256": hashlib.sha256(dsl.read_bytes()).hexdigest()})
        print(f"{bench.name:16s} {len(allowed):3d} allowed  outside: {unknown}")
    ver = subprocess.run([GCC, "--version"], capture_output=True, text=True).stdout.splitlines()[0]
    (args.crisp_dir / "manifest.json").write_text(json.dumps(
        {"compiler": ver, "flags": FLAGS, "embench": str(EMBENCH), "rv64im_instructions": len(isa),
         "workloads": records}, indent=2) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
