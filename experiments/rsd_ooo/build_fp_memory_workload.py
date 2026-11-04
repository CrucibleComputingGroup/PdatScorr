#!/usr/bin/env python3
"""Exercise FP register storage using FLW/FSW without FP arithmetic dispatch.

The Scheduler no-FP-operation contract permits these memory micro-ops; it does
not justify removal of the FP register file. Integer arithmetic checks exact
copied bit patterns, including signed zeros, infinities and NaN payloads.
"""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess

from build_workloads import generate, sha, MASK

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT/'fp_memory_workloads')
    parser.add_argument('--prefix', default='/home/allenjin/riscv/bin/riscv32-unknown-elf-')
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ, PATH='/usr/bin:/bin:/usr/local/bin')
    compiler = subprocess.check_output([args.prefix+'gcc', '--version'], text=True, env=env).splitlines()[0]
    rows = []
    count = 128
    special = [0x00000000, 0x80000000, 0x3f800000, 0xbf800000,
               0x7f800000, 0xff800000, 0x7fc12345, 0x7f812345]
    for seed in (1, 7, 42):
        source, _ = generate('stream_sum', seed, count)
        old = 'lw t0, 0(s0)\nlw t1, 0(s1)\nadd t2, t0, t1'
        assert source.count(old) == 1
        source = source.replace(old,
            'flw f0, 0(s0)\nflw f31, 0(s1)\n'
            'fsw f0, 0(s2)\nfsw f31, 4(s2)\n'
            'lw t0, 0(s2)\nlw t1, 4(s2)\nadd t2, t0, t1')
        source = source.replace('  csrw mtvec, t0\n',
                                '  csrw mtvec, t0\n  li t0, 0x6000\n  csrs mstatus, t0\n')
        code, data = source.split('inputs:\n')
        words = [int(x, 16) for x in re.findall(r'^\.word 0x([0-9a-f]+)$', data, re.M)]
        assert len(words) == 2*count
        words[:len(special)] = special
        expected = sum(((a+b)&MASK) for a,b in zip(words[:count], words[count:])) & MASK
        source = ('# FP-memory boundary test: all FP instructions are FLW/FSW.\n'
                  + code + 'inputs:\n' + ''.join(f'.word 0x{x:08x}\n' for x in words))
        out = output/f'fp_memory_only_s{seed}_n{count}'
        out.mkdir()
        (out/'code.S').write_text(source)
        (out/'link.ld').write_text('OUTPUT_ARCH(riscv)\nENTRY(_start)\nSECTIONS {\n'
            ' .text 0x1000 : { *(.text) }\n .rodata 0x8000 : { *(.rodata) }\n}\n')
        commands = [
            [args.prefix+'gcc', '-march=rv32imf_zicsr', '-mabi=ilp32', '-nostdlib',
             '-nostartfiles', '-Wl,--no-relax', '-T', str(out/'link.ld'),
             str(out/'code.S'), '-o', str(out/'code.elf')],
            [args.prefix+'objcopy', '-O', 'binary', str(out/'code.elf'), str(out/'code.rom.bin')],
        ]
        for command in commands:
            subprocess.run(command, check=True, env=env, capture_output=True)
        (out/'code.dump').write_bytes(subprocess.check_output(
            [args.prefix+'objdump', '-d', str(out/'code.elf')], env=env))
        binary = bytes(4096)+(out/'code.rom.bin').read_bytes()
        assert len(binary) <= 65536
        binary = binary.ljust(65536, b'\0')
        (out/'code.hex').write_text(''.join(binary[i:i+16][::-1].hex()+'\n'
                                         for i in range(0,len(binary),16)))
        row = dict(name=out.name, mode='fp_memory_only', seed=seed, count=count,
                   expected_serial=f'signature={expected:08x}\n', region_contract=False,
                   scheduler_contract='Actual scheduler writes exclude MOP_TYPE_FP; MOP_TYPE_MEM with FP registers remains allowed',
                   isa='rv32imf_zicsr', compiler=compiler, commands=commands,
                   fp_memory_instructions_per_completed_run=4*count,
                   oracle='Integer modular sum of the original raw input words after FLW/FSW copies',
                   hashes={f:sha(out/f) for f in ('code.S','code.elf','code.hex','link.ld')})
        (out/'manifest.json').write_text(json.dumps(row,indent=2)+'\n')
        rows.append(row)
    (output/'manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
    print(json.dumps({'workloads':len(rows),'output':str(output)}))


if __name__ == '__main__':
    main()
