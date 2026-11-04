#!/usr/bin/env python3
"""Build unchanged pre-FPU LEN5 RTL with its upstream bare testbench.

This smoke qualification is not architectural validation or an ODC experiment.
The external testbench FIFO parameter is fixed to the datapath default (2),
instead of upstream's latency-dependent expression. Core RTL is never edited.
"""
from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import time
from pathlib import Path

from prepare_frontend import PIN, PRE_FPU_PIN, digest, git, workspace_root

TB_FILES = (
    "tb/memory/memory_class.svh", "tb/memory/memory_if.sv",
    "tb/memory/memory_bare_emu.sv", "tb/len5_utils.svh", "tb/tb_bare.sv",
    "tb/verilator/len5_tb.cpp", "tb/verilator/tb_macros.cpp",
    "tb/verilator/tb_macros.hh", "tb/misc/tb-waivers.vlt",
)
SMOKE = """.option norvc
.section .text
.globl _start
_start:
    li t0, 0
    li t1, 0
    li t2, 64
1:  add t0, t0, t1
    addi t1, t1, 1
    bne t1, t2, 1b
    li t3, 2016
    bne t0, t3, fail
    li t4, 0x400
    sd t0, 0(t4)
    ld t5, 0(t4)
    bne t5, t3, fail
    ld a0, 8(t4)
    addi a2, a0, 1
    li a1, 31
    li a3, 32
    bne a0, a1, fail
    bne a2, a3, fail
    li t0, 0
    j exit
fail:
    li t0, 1
exit:
    li t1, 0x20000100
    sb t0, 0(t1)
2:  j 2b
.org 0x400
    .dword 0
    .dword 31
"""


def main() -> None:
    here = Path(__file__).resolve().parent
    external = workspace_root(here) / "experiments/bounded_dynamic"
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--deps", type=Path, default=external / "deps/len5")
    ap.add_argument("--frontend", type=Path, default=external / "len5/build/pre_fpu_frontend")
    ap.add_argument("--build", type=Path, default=external / "len5/build/pre_fpu_simulation_ooo")
    ap.add_argument("--verilator", default="/usr/bin/verilator")
    ap.add_argument("--compiler-prefix", default="riscv64-linux-gnu-")
    ap.add_argument("--jobs", type=int, default=2)
    ap.add_argument("--memory-pipe-num", type=int, default=2, help="Upstream memory-model stages; core fetch FIFO remains fixed at 2")
    ap.add_argument("--tb-compat", action="store_true", help="Remove erroneous const qualifiers on two upstream testbench variables assigned by methods")
    args = ap.parse_args()
    deps, frontend, build = args.deps.resolve(), args.frontend.resolve(), args.build.resolve()
    fm = json.loads((frontend / "manifest.json").read_text())
    assert fm["upstream_commit"] == PRE_FPU_PIN
    assert fm["status"] == "normalized_structural_check_passed"
    assert fm["original_sha256"] == fm["prepared_sha256"]
    assert git(deps, "rev-parse", "HEAD") == PIN
    assert not git(deps, "status", "--porcelain")
    build.mkdir(parents=True, exist_ok=True)
    sources = []
    source_hashes = {}
    for rel in (frontend / "sources.txt").read_text().splitlines():
        path = frontend / rel
        raw = path.read_bytes()
        assert digest(raw) == fm["prepared_sha256"][rel.removeprefix("source/")]
        dest = build / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(raw)
        sources.append(str(dest))
        source_hashes[rel] = digest(raw)
    tb_original, tb_prepared = {}, {}
    for rel in TB_FILES:
        raw = subprocess.check_output(["git", "-C", str(deps), "show", PRE_FPU_PIN + ":" + rel])
        tb_original[rel] = digest(raw)
        if rel == "tb/tb_bare.sv":
            old = "localparam int unsigned FetchMemIfFifoDepth = MemPipeNum + ((MemEmuSkipInstrOutReg) ? 0 : 2);"
            assert raw.count(old.encode()) == 1
            raw = raw.replace(old.encode(), b"localparam int unsigned FetchMemIfFifoDepth = 2;")
            old_memory = b"localparam int unsigned MemPipeNum = 0;"
            assert raw.count(old_memory) == 1
            raw = raw.replace(old_memory, f"localparam int unsigned MemPipeNum = {args.memory_pipe_num};".encode())
            assert raw.count(b"endmodule") == 1
            raw = raw.replace(b"endmodule", b'`include "qualification_monitor.svh"\nendmodule')
        if rel == "tb/memory/memory_class.svh" and args.tb_compat:
            for old in (b"const local int                        fd;", b"const local string                     file_line;"):
                assert raw.count(old) == 1
                raw = raw.replace(old, old.removeprefix(b"const "))
        if rel == "tb/len5_utils.svh" and args.tb_compat:
            old = b"expipe_pkg::rob_idx_t rob_idx = tb_len5_get_commit_idx();"
            assert raw.count(old) == 1
            raw = raw.replace(old, b"expipe_pkg::rob_idx_t rob_idx;\n  rob_idx = tb_len5_get_commit_idx();")
        dest = build / "source" / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(raw)
        tb_prepared[rel] = digest(raw)
    monitor = (here / "qualification_monitor.svh").read_bytes()
    (build / "source/tb/qualification_monitor.svh").write_bytes(monitor)
    verilator = str(Path(shutil.which(args.verilator) or args.verilator).resolve())
    command = [verilator, "--cc", "--exe", "--build", "-j", str(args.jobs),
               "--assert", "--trace-fst", "--trace-structs", "--x-assign", "unique",
               "--x-initial", "unique", "-Wno-fatal", "--top-module", "tb_bare",
               "--Mdir", str(build / "obj_dir"), "-GBOOT_PC=0",
               "-I" + str(build / "source/tb"), "-I" + str(build / "source/tb/memory"),
               "-CFLAGS", "-I" + str(build / "source/tb/verilator"), *sources,
               *[str(build / "source" / p) for p in TB_FILES if p.endswith((".sv", ".cpp", ".vlt"))]]
    manifest = {
        "purpose": "Simulator build and one self-checking RV64 integer smoke only; no Pscorr or correctness claim",
        "upstream_commit": PRE_FPU_PIN, "frontend_manifest_sha256": digest((frontend / "manifest.json").read_bytes()),
        "core_rtl_source_edits": False, "core_source_sha256": source_hashes,
        "capacity_parameters": fm["capacity_parameters_unchanged"],
        "testbench_changes": [{"path": "tb/tb_bare.sv", "change": "Fix FetchMemIfFifoDepth to 2, matching datapath default; set external MemPipeNum to CLI value; include read-only qualification monitor"}],
        "testbench_original_sha256": tb_original, "testbench_prepared_sha256": tb_prepared,
        "qualification_monitor_sha256": digest(monitor),
        "memory_pipe_num": args.memory_pipe_num, "fetch_fifo_depth": 2, "boot_pc": 0,
        "verilator_version": subprocess.check_output([verilator, "--version"], text=True).strip(),
        "verilator_sha256": digest(Path(verilator).read_bytes()), "build_command": command,
        "compiler_prefix": args.compiler_prefix,
        "build_environment": {"PATH_prefix": "/usr/bin:/bin", "reason": "Select host as/ld for host g++; inherited workspace PATH contains a bare RISC-V as before /usr/bin"},
        "validation_limit": "Upstream C++ returns 0 even on timeout or nonzero program exit; require success text, absence of failure/timeout/ERROR, and a nonempty commit trace.",
    }
    if args.tb_compat:
        manifest["testbench_changes"].append({"path": "tb/memory/memory_class.svh", "change": "Remove const on fd/file_line, which upstream assigns outside the constructor; leave memory_file_path const"})
        manifest["testbench_changes"].append({"path": "tb/len5_utils.svh", "change": "Assign rob_idx at every trace-function call instead of once via static variable initialization; affects trace monitor only"})
    start = time.monotonic()
    child_env = {**os.environ, "PATH": "/usr/bin:/bin:" + os.environ.get("PATH", "")}
    with (build / "build.log").open("w") as log:
        proc = subprocess.run(command, cwd=build, env=child_env, stdout=log, stderr=subprocess.STDOUT)
    manifest.update(build_returncode=proc.returncode, build_seconds=time.monotonic() - start,
                    build_log_sha256=digest((build / "build.log").read_bytes()))
    # Preserve successful build provenance even if a later compiler/run command fails.
    (build / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    if proc.returncode == 0:
        (build / "smoke.S").write_text(SMOKE)
        compile_commands = [
            [args.compiler_prefix + "gcc", "-march=rv64im", "-mabi=lp64", "-nostdlib", "-static", "-Wl,-Ttext=0", "-Wl,--build-id=none", "smoke.S", "-o", "smoke.elf"],
            [args.compiler_prefix + "objcopy", "-O", "verilog", "smoke.elf", "smoke.hex"],
        ]
        with (build / "compile.log").open("w") as log:
            for cmd in compile_commands:
                subprocess.run(cmd, cwd=build, env=child_env, stdout=log, stderr=subprocess.STDOUT, check=True)
        run = [str(build / "obj_dir/Vtb_bare"), "+firmware=" + str(build / "smoke.hex"),
               "--max_cycles=10000", "--dump_waves=false", "--dump_trace=true", "--log_level=LOG_LOW"]
        with (build / "run.log").open("w") as log:
            sim = subprocess.run(run, cwd=build, stdout=log, stderr=subprocess.STDOUT, timeout=60)
        out = (build / "run.log").read_text()
        trace = build / "logs/sim-trace.log"
        passed = (sim.returncode == 0 and "Program exit with code: 0x00 (SUCCESS)" in out
                  and "Simulation completed successfully" in out
                  and "FAILURE" not in out and "timeout" not in out.lower()
                  and "ERROR" not in out
                  and trace.is_file() and trace.stat().st_size > 0)
        manifest.update(compile_commands=compile_commands, run_command=run,
                        run_returncode=sim.returncode, smoke_passed=passed,
                        smoke_source_sha256=digest(SMOKE.encode()),
                        run_log_sha256=digest((build / "run.log").read_bytes()),
                        binary_sha256=digest((build / "obj_dir/Vtb_bare").read_bytes()),
                        firmware_sha256=digest((build / "smoke.hex").read_bytes()),
                        trace_sha256=digest(trace.read_bytes()) if trace.exists() else None)
    assert not git(deps, "status", "--porcelain")
    (build / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps({k: manifest.get(k) for k in ("build_returncode", "build_seconds", "run_returncode", "smoke_passed")}))
    if not manifest.get("smoke_passed"):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
