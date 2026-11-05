#!/usr/bin/env python3
"""Screen arbitrary repetition within the streaming instruction-word alphabet.

This is a different program from the streaming kernel. A finite slot witness
can refute a proposed alphabet-wide bound without refuting the exact kernel.
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
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from prepare_frontend import PRE_FPU_PIN, digest, workspace_root
from run_div_falsifier import extract
from run_streaming import stores
from analyze_fetch_spacing import native_edges, timing, write_csv


def main():
    here = Path(__file__).resolve().parent
    external = workspace_root(here) / 'experiments/bounded_dynamic/len5/build'
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--simulator-build', type=Path, default=external/'pre_fpu_simulation_fetchgap2_v1')
    parser.add_argument('--alphabet-disassembly', type=Path, default=here.parent/'results/streaming_fetchgap2_v2/program.disasm')
    parser.add_argument('--repetitions', type=int, choices=(32, 64), default=64)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--evidence', type=Path, required=True)
    args = parser.parse_args()
    build, out, evidence = args.simulator_build.resolve(), args.output.resolve(), args.evidence.resolve()
    manifest = json.loads((build/'manifest.json').read_text())
    binary = build/'obj_dir/Vtb_bare'
    assert manifest['upstream_commit'] == PRE_FPU_PIN and not manifest['core_rtl_source_edits']
    assert manifest['smoke_passed'] and manifest['binary_sha256'] == digest(binary.read_bytes())
    assert manifest['instruction_min_accept_spacing'] == 2
    assert manifest['memory_pipe_num'] == 2 and manifest['fetch_fifo_depth'] == 2
    alphabet = {int(word, 16) for address, word in re.findall(
        r'(?m)^\s*([0-9a-f]+):\s+([0-9a-f]{8})\s', args.alphabet_disassembly.read_text()) if int(address, 16) < 0x38}
    assert len(alphabet) == 14
    out.mkdir(parents=True, exist_ok=False)
    evidence.mkdir(parents=True, exist_ok=False)
    assembly = f'''.option norvc
.option norelax
.section .text
.globl _start
_start:
    lui s0, 0x1
    .rept {args.repetitions}
    addi s0, s0, 8
    .endr
    lui t0, 0x20000
    addiw t0, t0, 256
    sb zero, 0(t0)
halt:
    jal zero, halt
// Map speculative fetches after the halt with words from the same alphabet.
    .rept 64
    .word 0x0000006f
    .endr
'''
    (out/'program.S').write_text(assembly)
    (out/'run_alphabet_falsifier.py').write_bytes(Path(__file__).read_bytes())
    env = {**os.environ, 'PATH': '/usr/bin:/bin:/usr/local/bin'}
    commands = [
        ['riscv64-linux-gnu-gcc', '-march=rv64im', '-mabi=lp64', '-nostdlib', '-static',
         '-Wl,-Ttext=0', '-Wl,--build-id=none', 'program.S', '-o', 'program.elf'],
        ['riscv64-linux-gnu-objcopy', '-O', 'verilog', 'program.elf', 'program.hex']]
    with (out/'compile.log').open('w') as log:
        for command in commands:
            subprocess.run(command, cwd=out, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
    with (out/'program.disasm').open('w') as log:
        subprocess.run(['riscv64-linux-gnu-objdump', '-d', 'program.elf'], cwd=out, env=env, stdout=log, check=True)
    words = [int(word, 16) for word in re.findall(r'(?m)^\s*[0-9a-f]+:\s+([0-9a-f]{8})\s', (out/'program.disasm').read_text())]
    assert len(words) == args.repetitions + 69 and set(words) <= alphabet
    run = [str(binary), '+firmware='+str(out/'program.hex'), '--max_cycles=2000',
           '--dump_waves=true', '--dump_trace=true', '--log_level=LOG_LOW']
    with (out/'run.log').open('w') as log:
        process = subprocess.run(run, cwd=out, env=env, stdout=log, stderr=subprocess.STDOUT, timeout=30)
    text = (out/'run.log').read_text()
    exit_ok = process.returncode == 0 and 'Program exit with code: 0x00 (SUCCESS)' in text
    assert exit_ok and not any(word in text.lower() for word in ('error', 'failure', 'timeout'))
    subprocess.run(['/usr/bin/fst2vcd', str(out/'logs/waves.fst'), '-o', str(out/'all.vcd')], check=True, capture_output=True)
    occupancy = extract(out/'all.vcd', evidence/'rs_state.vcd', evidence/'occupancy.csv')
    rows = native_edges(out/'all.vcd')
    platform, fetches, loads = timing(rows, 2)
    assert not loads and not platform['load_pending_at_end']
    assert not any(row['fetch_exception'] or row['load_exception'] for row in rows if row['reset_n'])
    writes = stores(out/'all.vcd')
    assert [{k: v for k, v in row.items() if k != 'time'} for row in writes] == [
        {'data_store_addr_o': 0x20000100, 'data_store_wdata_o': 0, 'data_store_be_o': 1}]
    retired = []
    for pc, instruction, register, value in re.findall(
            r'(?m)^core\s+0:\s+\d+\s+0x([0-9a-f]+)\s+\(0x([0-9a-f]+)\)\s+x(\d+)\s+0x([0-9a-f]+)',
            (out/'logs/sim-trace.log').read_text()):
        if int(instruction, 16) == 0x00840413:
            retired.append({'pc': int(pc, 16), 'instruction': int(instruction, 16),
                            'register': int(register), 'value': int(value, 16)})
    expected = [{'pc': 4*(i+1), 'instruction': 0x00840413, 'register': 8, 'value': 0x1000+8*(i+1)}
                for i in range(args.repetitions)]
    assert retired == expected
    write_csv(evidence/'retired_addi.csv', retired)
    write_csv(evidence/'native_platform_edges.csv', rows)
    write_csv(evidence/'fetch_response_intervals.csv', fetches)
    write_csv(evidence/'accepted_stores.csv', writes)
    occupancy_rows = list(csv.DictReader((evidence/'occupancy.csv').open()))
    allocations = [row for row in occupancy_rows if row['insert'] == '1']
    indices = sorted({int(row['new_idx']) for row in allocations})
    lower = [row for row in allocations if int(row['new_idx']) < 4]
    for name in ('program.S', 'program.hex', 'program.disasm', 'compile.log', 'run.log', 'run_alphabet_falsifier.py',
                 'logs/qualification_events.csv', 'logs/sim-trace.log', 'logs/platform_edges.csv'):
        target = evidence/name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(out/name, target)
    shutil.copyfile(build/'manifest.json', evidence/'simulator_manifest.json')
    summary = {
        'scope': 'Finite counterexample screen for arbitrary sequences from the streaming alphabet; different program, not a counterexample to the exact streaming kernel',
        'program_exit_ok': exit_ok, 'all_dependent_addi_retired_values_checked': retired == expected,
        'repetitions': args.repetitions, 'same_14_word_alphabet': sorted(f'{word:08x}' for word in alphabet),
        'all_program_words_in_alphabet': True, 'allocated_alu_indices': indices,
        'falsifies_no_allocation_to_indices_0_through_3': bool(lower),
        'first_low_slot_allocation': lower[0] if lower else None,
        'occupancy': occupancy, 'platform': platform,
        'reported_cpu_cycles': int(re.search(r'total CPU cycles:\s+(\d+)', text).group(1)),
        'all_fetch_and_load_exception_flags_zero': True,
        'compile_commands': commands, 'run_command': run, 'run_returncode': process.returncode,
        'core_rebuilt': False, 'core_rtl_source_edits': False,
        'capacity_parameters': manifest['capacity_parameters'],
        'binary_sha256': manifest['binary_sha256'], 'simulator_manifest_sha256': digest((build/'manifest.json').read_bytes()),
        'alphabet_disassembly_sha256': digest(args.alphabet_disassembly.read_bytes()),
        'source_hashes': {str(path): digest(path.read_bytes()) for path in
                          [Path(__file__), here/'run_streaming.py', here/'analyze_fetch_spacing.py', here.parent/'run_div_falsifier.py']},
        'raw_run_directory': str(out), 'raw_fst_sha256': digest((out/'logs/waves.fst').read_bytes()),
        'raw_vcd_sha256': digest((out/'all.vcd').read_bytes()),
        'artifact_sha256': {str(path.relative_to(evidence)): digest(path.read_bytes()) for path in evidence.rglob('*') if path.is_file()}}
    (evidence/'summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    (evidence/'SHA256SUMS').write_text(''.join(f'{digest(path.read_bytes())}  {path.relative_to(evidence)}\n'
        for path in sorted(evidence.rglob('*')) if path.is_file() and path.name != 'SHA256SUMS'))
    print(json.dumps({key: summary[key] for key in ('program_exit_ok', 'all_dependent_addi_retired_values_checked',
        'allocated_alu_indices', 'falsifies_no_allocation_to_indices_0_through_3', 'reported_cpu_cycles')}))
    print(json.dumps({'max_live_ALU': occupancy['max_live_entries'], 'first_low_slot': summary['first_low_slot_allocation']}))


if __name__ == '__main__':
    main()
