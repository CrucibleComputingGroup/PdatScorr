#!/usr/bin/env python3
"""Run a self-checking DIV/ALU-RS occupancy falsifier on the existing simulator.

No core or testbench rebuild occurs. FST exposes actual RS state and handshakes;
all new files go into fresh run/evidence directories.
"""
from __future__ import annotations
import argparse
import csv
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
from prepare_frontend import PRE_FPU_PIN, digest, workspace_root

ASM = """.option norvc
.option norelax
.section .text
.globl _start
_start:
    li t4, 0x400
    ld t5, 0(t4)
    li t6, 3
    bne t5, t6, fail
    li t0, -1
    divu t2, t0, t5
consumers:
    addi a0, t2, 1
    addi a1, t2, 2
    addi a2, t2, 3
    addi a3, t2, 4
    addi a4, t2, 5
    addi a5, t2, 6
    addi a6, t2, 7
    addi a7, t2, 8
    li t3, 0x5555555555555555
    bne t2, t3, fail
    addi t3, t3, 1
    bne a0, t3, fail
    addi t3, t3, 1
    bne a1, t3, fail
    addi t3, t3, 1
    bne a2, t3, fail
    addi t3, t3, 1
    bne a3, t3, fail
    addi t3, t3, 1
    bne a4, t3, fail
    addi t3, t3, 1
    bne a5, t3, fail
    addi t3, t3, 1
    bne a6, t3, fail
    addi t3, t3, 1
    bne a7, t3, fail
    li t0, 0
    j exit
fail:
    li t0, 1
exit:
    li t1, 0x20000100
    sb t0, 0(t1)
1:  j 1b
.org 0x400
    .dword 3
"""


def extract(vcd: Path, selected: Path, occupancy: Path) -> dict:
    prefix = "TOP.tb_bare.u_datapath.u_backend.u_exec_stage.u_alu_unit.u_arith_rs."
    state_names = [prefix + f"curr_state[{i}]" for i in range(8)]
    required = set(state_names + [prefix+x for x in ("insert", "new_idx", "remove", "cdb_idx")]
                   + ["TOP.tb_bare.clk_i", "TOP.tb_bare.rst_ni", "TOP.tb_bare.curr_cycle"])
    names, widths, scopes, selected_codes, header = {}, {}, [], set(), []
    samples, values, previous = [], {}, {}
    time = 0
    def number(name, source):
        raw = source.get(names[name], "x")
        return None if any(c in raw.lower() for c in "xz") else int(raw, 2)
    def flush():
        nonlocal previous
        if names and number("TOP.tb_bare.clk_i", values) == 1 and number("TOP.tb_bare.clk_i", previous) == 0:
            if number("TOP.tb_bare.rst_ni", values) == 1 and number("TOP.tb_bare.rst_ni", previous) == 1:
                before = [number(n, previous) for n in state_names]
                after = [number(n, values) for n in state_names]
                assert None not in before + after, "Unknown active RS state"
                samples.append({"time": time, "cycle_pre_edge": number("TOP.tb_bare.curr_cycle", previous),
                                "insert": number(prefix+"insert", previous),
                                "new_idx": number(prefix+"new_idx", previous),
                                "remove": number(prefix+"remove", previous),
                                "cdb_idx": number(prefix+"cdb_idx", previous),
                                "live_pre": sum(x != 0 for x in before),
                                "live_post": sum(x != 0 for x in after),
                                "states_post": after})
        previous = dict(values)
    with vcd.open() as src, selected.open("w") as dst:
        for line in src:
            words = line.split()
            if words and words[0] == "$scope": scopes.append(words[2])
            elif words and words[0] == "$upscope": scopes.pop()
            if words and words[0] == "$var":
                name = (".".join(scopes+[words[4]])).replace(".[", "[")
                if name in required or (name.startswith(prefix+"data[") and name.endswith((".dest_rob_idx", ".rs1_rob_idx"))):
                    names[name] = words[3]
                    widths[words[3]] = int(words[2])
                    selected_codes.add(words[3])
                    dst.write(line)
            else:
                dst.write(line)
            if words and words[0] == "$enddefinitions": break
        assert required <= set(names), sorted(required-set(names))
        for line in src:
            line = line.rstrip()
            if line.startswith("#"):
                flush()
                time = int(line[1:])
                dst.write(line+"\n")
            elif line.startswith(("b", "B")):
                value, code = line[1:].split()
                if code in selected_codes:
                    values[code] = value
                    dst.write(line+"\n")
            elif line and line[0] in "01xXzZ":
                code = line[1:]
                if code in selected_codes:
                    values[code] = line[0]
                    dst.write(line+"\n")
            elif line.startswith("$"): dst.write(line+"\n")
        flush()
    with occupancy.open("w") as out:
        writer = csv.DictWriter(out, fieldnames=list(samples[0]))
        writer.writeheader()
        for sample in samples:
            writer.writerow({**sample, "states_post": " ".join(map(str, sample["states_post"]))})
    fullest = max(samples, key=lambda x:x["live_post"])
    all_pending = [s for s in samples if s["states_post"] == [1]*8]
    return {"max_live_entries": fullest["live_post"], "first_maximum": fullest,
            "all_eight_rs1_pending": bool(all_pending), "first_all_pending": all_pending[0] if all_pending else None,
            "state_encoding": {"EMPTY": 0, "RS1_PENDING": 1},
            "selected_signal_names": sorted(names)}


def main():
    here = Path(__file__).resolve().parent
    external = workspace_root(here)/"experiments/bounded_dynamic/len5/build"
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--simulator-build", type=Path, default=external/"pre_fpu_simulation_ooo")
    ap.add_argument("--output", type=Path, default=external/"div_falsifier_v1")
    ap.add_argument("--evidence", type=Path, default=here/"results/div_falsifier_v1")
    ap.add_argument("--compiler-prefix", default="riscv64-linux-gnu-")
    ap.add_argument("--fst2vcd", default="/usr/bin/fst2vcd")
    args = ap.parse_args()
    build, out, evidence = args.simulator_build.resolve(), args.output.resolve(), args.evidence.resolve()
    m = json.loads((build/"manifest.json").read_text())
    binary = build/"obj_dir/Vtb_bare"
    assert m["upstream_commit"] == PRE_FPU_PIN and m["core_rtl_source_edits"] is False
    assert m["smoke_passed"] and digest(binary.read_bytes()) == m["binary_sha256"]
    assert m["memory_pipe_num"] == 2 and m["fetch_fifo_depth"] == 2
    out.mkdir(parents=True, exist_ok=False)
    evidence.mkdir(parents=True, exist_ok=False)
    (out/"program.S").write_text(ASM)
    env = {**os.environ, "PATH": "/usr/bin:/bin:"+os.environ.get("PATH", "")}
    commands = [[args.compiler_prefix+"gcc", "-march=rv64im", "-mabi=lp64", "-nostdlib", "-static", "-Wl,-Ttext=0", "-Wl,--build-id=none", "program.S", "-o", "program.elf"],
                [args.compiler_prefix+"objcopy", "-O", "verilog", "program.elf", "program.hex"]]
    with (out/"compile.log").open("w") as log:
        for cmd in commands: subprocess.run(cmd, cwd=out, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
    with (out/"program.disasm").open("w") as log:
        subprocess.run([args.compiler_prefix+"objdump", "-d", "program.elf"], cwd=out, env=env, stdout=log, check=True)
    run = [str(binary), "+firmware="+str(out/"program.hex"), "--max_cycles=2000", "--dump_waves=true", "--dump_trace=true", "--log_level=LOG_LOW"]
    with (out/"run.log").open("w") as log:
        proc = subprocess.run(run, cwd=out, env=env, stdout=log, stderr=subprocess.STDOUT, timeout=60)
    log_text = (out/"run.log").read_text()
    passed = proc.returncode == 0 and "Program exit with code: 0x00 (SUCCESS)" in log_text and "ERROR" not in log_text and "FAILURE" not in log_text and "timeout" not in log_text.lower()
    conversion = [args.fst2vcd, str(out/"logs/waves.fst"), "-o", str(out/"all.vcd")]
    subprocess.run(conversion, check=True, capture_output=True)
    witness = extract(out/"all.vcd", evidence/"rs_state.vcd", evidence/"occupancy.csv")
    events = list(csv.DictReader((out/"logs/qualification_events.csv").open()))
    requests = [e for e in events if e["event"] == "LOAD_REQUEST"]
    responses = [e for e in events if e["event"] == "LOAD_RESPONSE"]
    assert len(requests) == len(responses) == 1
    response_latency = int(responses[0]["cycle"])-int(requests[0]["cycle"])
    for rel in ("program.S", "program.hex", "program.disasm", "compile.log", "run.log", "logs/qualification_events.csv", "logs/sim-trace.log"):
        dest = evidence/rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(out/rel,dest)
    summary = {"scope": "Negative finite architectural trace: prompt memory service alone does not exclude any ALU RS slot. No optimization result or universal proof.",
               "upstream_commit": PRE_FPU_PIN, "simulator_manifest_sha256": digest((build/"manifest.json").read_bytes()),
               "binary_sha256": m["binary_sha256"], "core_rebuilt": False, "core_rtl_source_edits": False,
               "capacities": m["capacity_parameters"], "memory_pipe_num": 2, "fetch_fifo_depth": 2,
               "run_returncode": proc.returncode, "program_checks_passed": passed,
               "expected_dividend": "0xffffffffffffffff", "expected_divisor": 3,
               "expected_quotient": "0x5555555555555555", "consumer_immediates": list(range(1,9)),
               "actual_memory_load_response_latency_cycles": response_latency,
               "compile_commands": commands, "run_command": run, "conversion_command": conversion,
               "raw_fst_sha256": digest((out/"logs/waves.fst").read_bytes()),
               "raw_vcd_sha256": digest((out/"all.vcd").read_bytes()),
               "witness": witness, "script_sha256": digest(Path(__file__).read_bytes()),
               "artifact_sha256": {str(p.relative_to(evidence)):digest(p.read_bytes()) for p in evidence.rglob("*") if p.is_file()}}
    (evidence/"summary.json").write_text(json.dumps(summary, indent=2)+"\n")
    print(json.dumps({"program_checks_passed": passed, "load_latency": response_latency, "witness": {k:witness[k] for k in ("max_live_entries","all_eight_rs1_pending","first_all_pending")}}))
    if not passed or not witness["all_eight_rs1_pending"]: raise SystemExit(1)


if __name__ == "__main__":
    main()
