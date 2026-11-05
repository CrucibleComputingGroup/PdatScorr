#!/usr/bin/env python3
"""Screen an input-dependent streaming kernel on unchanged, qualified LEN5.

This is a finite simulation and candidate screen, never an occupancy proof.
Output stores are checked by the host, so the program does not read its output.
"""
from __future__ import annotations

import argparse
import csv
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from prepare_frontend import PRE_FPU_PIN, digest, workspace_root
from run_div_falsifier import extract

COUNT = 64
MASK = (1 << 64) - 1
INPUT = [((i * 0x9e3779b97f4a7c15) ^ (i << 17)) & MASK for i in range(COUNT)]
ASM = """.option norvc
.option norelax
.section .text
.globl _start
_start:
    li s0, 0x1000
    li s1, 0x2000
    li s2, 64
loop:
    ld a0, 0(s0)
    addi a1, a0, 1
    sd a1, 0(s1)
    addi s0, s0, 8
    addi s1, s1, 8
    addi s2, s2, -1
    bnez s2, loop
    li t0, 0x20000100
    sb zero, 0(t0)
halt:
    j halt
.org 0x1000
""" + "".join(f"    .dword 0x{x:016x}\n" for x in INPUT) + """
// Explicitly mapped input RAM padding for speculative reads past the loop.
// It is outside the 64-element application input and is never an output check.
.org 0x1200
    .zero 128
"""


def stores(vcd: Path) -> list[dict]:
    """Read accepted native store requests at their sampling edge."""
    prefix = "TOP.tb_bare.u_datapath."
    signals = {x: prefix + x for x in (
        "clk_i", "rst_ni", "data_store_req_o", "data_store_gnt_i",
        "data_store_addr_o", "data_store_wdata_o", "data_store_be_o")}
    names, values, previous, scopes, rows = {}, {}, {}, [], []
    current_time = 0

    def number(key, state):
        raw = state.get(names[key], "x")
        return None if any(c in raw.lower() for c in "xz") else int(raw, 2)

    def flush():
        nonlocal previous
        if (number("clk_i", values) == 1 and number("clk_i", previous) == 0
                and number("rst_ni", previous) == 1
                and number("data_store_req_o", previous) == 1
                and number("data_store_gnt_i", previous) == 1):
            row = {k: number(k, previous) for k in (
                "data_store_addr_o", "data_store_wdata_o", "data_store_be_o")}
            if None in row.values():
                raise ValueError("Unknown accepted store payload")
            rows.append({"time": current_time, **row})
        previous = dict(values)

    with vcd.open() as source:
        for line in source:
            words = line.split()
            if words and words[0] == "$scope": scopes.append(words[2])
            elif words and words[0] == "$upscope": scopes.pop()
            elif words and words[0] == "$var":
                full = ".".join(scopes + [words[4]])
                for key, wanted in signals.items():
                    if full == wanted: names[key] = words[3]
            if words and words[0] == "$enddefinitions": break
        if set(names) != set(signals):
            raise ValueError(f"Missing native signals: {set(signals)-set(names)}")
        codes = set(names.values())
        for line in source:
            line = line.rstrip()
            if line.startswith("#"):
                flush()
                current_time = int(line[1:])
            elif line.startswith(("b", "B")):
                value, code = line[1:].split()
                if code in codes: values[code] = value
            elif line and line[0] in "01xXzZ" and line[1:] in codes:
                values[line[1:]] = line[0]
        flush()
    return rows


def main():
    here = Path(__file__).resolve().parent
    external = workspace_root(here) / "experiments/bounded_dynamic/len5/build"
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--simulator-build", type=Path, default=external/"pre_fpu_simulation_ooo")
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--evidence", type=Path, required=True)
    args = ap.parse_args()
    build, out, evidence = args.simulator_build.resolve(), args.output.resolve(), args.evidence.resolve()
    manifest = json.loads((build/"manifest.json").read_text())
    binary = build/"obj_dir/Vtb_bare"
    assert manifest["upstream_commit"] == PRE_FPU_PIN
    assert manifest["core_rtl_source_edits"] is False and manifest["smoke_passed"]
    assert manifest["binary_sha256"] == digest(binary.read_bytes())
    out.mkdir(parents=True, exist_ok=False)
    evidence.mkdir(parents=True, exist_ok=False)
    (out/"run_streaming.py").write_bytes(Path(__file__).read_bytes())
    (out/"program.S").write_text(ASM)
    env = {**os.environ, "PATH": "/usr/bin:/bin:/usr/local/bin"}
    commands = [
        ["riscv64-linux-gnu-gcc", "-march=rv64im", "-mabi=lp64", "-nostdlib", "-static",
         "-Wl,-Ttext=0", "-Wl,--build-id=none", "program.S", "-o", "program.elf"],
        ["riscv64-linux-gnu-objcopy", "-O", "verilog", "program.elf", "program.hex"],
    ]
    with (out/"compile.log").open("w") as log:
        for cmd in commands:
            subprocess.run(cmd, cwd=out, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
    with (out/"program.disasm").open("w") as log:
        subprocess.run(["riscv64-linux-gnu-objdump", "-d", "program.elf"], cwd=out,
                       env=env, stdout=log, check=True)
    run = [str(binary), "+firmware="+str(out/"program.hex"), "--max_cycles=10000",
           "--dump_waves=true", "--dump_trace=true", "--log_level=LOG_LOW"]
    with (out/"run.log").open("w") as log:
        p = subprocess.run(run, cwd=out, env=env, stdout=log, stderr=subprocess.STDOUT, timeout=60)
    log = (out/"run.log").read_text()
    exit_ok = (p.returncode == 0 and "Program exit with code: 0x00 (SUCCESS)" in log
               and not any(t in log for t in ("ERROR", "FAILURE")) and "timeout" not in log.lower())
    subprocess.run(["/usr/bin/fst2vcd", str(out/"logs/waves.fst"), "-o", str(out/"all.vcd")],
                   check=True, capture_output=True)
    occupancy = extract(out/"all.vcd", evidence/"rs_state.vcd", evidence/"occupancy.csv")
    writes = stores(out/"all.vcd")
    expected = [{"data_store_addr_o": 0x2000+i*8, "data_store_wdata_o": (x+1)&MASK,
                 "data_store_be_o": 255} for i,x in enumerate(INPUT)]
    expected.append({"data_store_addr_o": 0x20000100, "data_store_wdata_o": 0, "data_store_be_o": 1})
    observed = [{k:v for k,v in row.items() if k != "time"} for row in writes]
    stores_ok = observed == expected
    with (evidence/"accepted_stores.csv").open("w") as f:
        writer = csv.DictWriter(f, fieldnames=list(writes[0]) if writes else ["time"])
        writer.writeheader(); writer.writerows(writes)
    for rel in ("program.S", "program.hex", "program.disasm", "compile.log", "run.log", "run_streaming.py",
                "logs/qualification_events.csv", "logs/sim-trace.log"):
        dst = evidence/rel; dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(out/rel, dst)
    summary = {
        "scope": "Finite kernel simulation and candidate screen only; no proof or optimization",
        "upstream_commit": PRE_FPU_PIN, "core_rtl_source_edits": False,
        "simulator_manifest_sha256": digest((build/"manifest.json").read_bytes()),
        "binary_sha256": manifest["binary_sha256"], "capacity_parameters": manifest["capacity_parameters"],
        "memory_pipe_num": manifest["memory_pipe_num"], "fetch_fifo_depth": manifest["fetch_fifo_depth"],
        "program": "64-element uint64 streaming increment; load-only input, store-only output",
        "input_ram_padding": {"start": "0x1200", "bytes": 128, "initial_value": 0,
                              "reason": "Map speculative reads past the final loop iteration; no instruction changes"},
        "input_values": INPUT, "program_exit_ok": exit_ok, "all_64_output_stores_and_exit_checked": stores_ok,
        "store_count": len(writes), "occupancy": occupancy,
        "compile_commands": commands, "run_command": run,
        "raw_fst_sha256": digest((out/"logs/waves.fst").read_bytes()),
        "script_sha256": digest(Path(__file__).read_bytes()),
        "artifact_sha256": {str(f.relative_to(evidence)):digest(f.read_bytes()) for f in evidence.rglob("*") if f.is_file()},
    }
    (evidence/"summary.json").write_text(json.dumps(summary, indent=2)+"\n")
    print(json.dumps({"exit_ok": exit_ok, "stores_ok": stores_ok, "store_count": len(writes),
                      "max_live_ALU": occupancy["max_live_entries"]}))
    return 0 if exit_ok and stores_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
