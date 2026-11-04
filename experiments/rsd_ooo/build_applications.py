#!/usr/bin/env python3
"""Build validation-only CoreMark and Dhrystone ports from retained vendor sources.

No certified performance scores: the vendored Ibex CoreMark source already
disables its minimum-ten-second rule. Algorithm and CRC checks are unchanged.
Dhrystone keeps its upstream 500 iterations, separate compilation, no-inline
pragma, and final-state expectations; only its silent debug printer is enabled.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
PROJECT = ROOT.parent.parent
CORE = PROJECT/'code/PdatProject/ibex/vendor/eembc_coremark'
DHRY = PROJECT/'code/PdatProject/ibex/vendor/riscv-tests/benchmarks/dhrystone'

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path, default=ROOT/'applications')
    p.add_argument('--prefix', default='/home/allenjin/riscv/bin/riscv32-unknown-elf-')
    p.add_argument('--coremark-iterations', type=int, default=10)
    args = p.parse_args()
    args.output.mkdir(exist_ok=False)
    env = dict(os.environ, PATH='/usr/bin:/bin:/usr/local/bin')
    compiler = subprocess.check_output([args.prefix+'gcc', '--version'], env=env, text=True).splitlines()[0]
    rows = []
    for name in ('coremark', 'dhrystone'):
        out = args.output/name
        originals = out/'originals'
        source = out/'source'
        originals.mkdir(parents=True)
        source.mkdir()
        source_map = {}
        inputs = [CORE/'coremark.h', CORE/'barebones/core_portme.h', CORE/'barebones/ee_printf.c']
        if name == 'coremark':
            inputs += [CORE/f for f in ('core_main.c','core_list_join.c','core_matrix.c','core_state.c','core_util.c','LICENSE.md','README.md')]
            inputs += [CORE.parent/'eembc_coremark.lock.hjson']
        else:
            inputs += [DHRY/f for f in ('dhrystone.c','dhrystone_main.c','dhrystone.h')]
            inputs += [DHRY.parent.parent/'LICENSE']
        for path in inputs:
            shutil.copy2(path, originals/path.name)
            shutil.copy2(path, source/path.name)
            source_map[path.name] = {'path':str(path.relative_to(PROJECT)), 'sha256':sha(path)}
        for path in (ROOT/'application_port').iterdir():
            shutil.copy2(path, source/path.name)
        h = source/'core_portme.h'
        h.write_text('#include <stddef.h>\n'+h.read_text())
        printf = source/'ee_printf.c'
        text = printf.read_text()
        old = '#error "You must implement the method uart_send_char to use this file!\\n";'
        assert text.count(old) == 1
        printf.write_text(text.replace(old, '*(volatile unsigned char *)0x40002000 = c;'))
        adaptations = ['RSD ROM/RAM loader and UART port', 'mcycle timing', 'freestanding bytewise libc subset',
                       'barebones header includes stddef.h; configuration set by compiler flags']
        if name == 'dhrystone':
            f = source/'dhrystone.c'
            text = f.read_text()
            old = 'void debug_printf(const char* str, ...)\n{\n}\n'
            assert text.count(old) == 1
            f.write_text(text.replace(old, '/* Printer supplied by RSD ee_printf port. */\n'))
            f = source/'dhrystone_main.c'
            text = f.read_text().replace('void debug_printf(const char* str, ...);', 'int debug_printf(const char* str, ...);')
            old = 'User_Time = End_Time - Begin_Time;'
            assert text.count(old) == 1
            f.write_text(text.replace(old, old+'\n    printf("ROI cycles: %lu\\n", (unsigned long)User_Time);'))
            adaptations += ['enable original debug_printf calls via ee_printf', 'print existing User_Time cycle delta']
        flags = ['-march=rv32im_zicsr','-mabi=ilp32','-O2','-g','-ffreestanding','-fno-builtin',
                 '-fno-stack-protector','-fno-common','-msmall-data-limit=0','-mstrict-align','-mno-relax',
                 '-std=gnu99','-Wno-implicit-int','-Wno-implicit-function-declaration',
                 '-DHAS_FLOAT=0','-DHAS_TIME_H=0','-DUSE_CLOCK=0','-DHAS_STDIO=0',
                 '-DHAS_PRINTF=0','-DMEM_METHOD=MEM_STATIC','-DMAIN_HAS_NOARGC=1',
                 '-DVALIDATION_RUN=1','-DTOTAL_DATA_SIZE=2000',f'-DITERATIONS={args.coremark_iterations}',
                 '-DCOMPILER_FLAGS="-O2 -march=rv32im_zicsr -mabi=ilp32 -fno-builtin; no LTO"',
                 '-DMEM_LOCATION="STATIC"','-I'+str(source)]
        files = ['start.S','runtime.c','ee_printf.c']
        if name == 'coremark':
            files += ['core_portme.c','core_main.c','core_list_join.c','core_matrix.c','core_state.c','core_util.c']
        else:
            files += ['dhrystone_main.c','dhrystone.c']
            flags += ['-Dprintf=ee_printf','-Ddebug_printf=ee_printf']
        commands = []
        objects = []
        with (out/'build.log').open('wb') as log:
            def run(cmd):
                commands.append(cmd)
                log.write(('COMMAND '+json.dumps(cmd)+'\n').encode()); log.flush()
                subprocess.run(cmd, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
            for f in files:
                obj = out/(Path(f).stem+'.o')
                run([args.prefix+'gcc', *flags, '-c', str(source/f), '-o', str(obj)])
                objects.append(str(obj))
            run([args.prefix+'gcc', '-march=rv32im_zicsr','-mabi=ilp32','-nostdlib','-nostartfiles',
                 '-Wl,--no-relax','-Wl,-Map='+str(out/'code.map'),'-T',str(source/'link.ld'),
                 *objects,'-lgcc','-o',str(out/'code.elf')])
            run([args.prefix+'objcopy','-O','binary',str(out/'code.elf'),str(out/'code.rom.bin')])
        (out/'code.dump').write_bytes(subprocess.check_output([args.prefix+'objdump','-d',str(out/'code.elf')],env=env))
        data = bytes(4096)+(out/'code.rom.bin').read_bytes()
        assert len(data) <= 65536, len(data)
        data = data.ljust(65536,b'\0')
        (out/'code.hex').write_text(''.join(data[i:i+16][::-1].hex()+'\n' for i in range(0,len(data),16)))
        row = dict(name=name, compiler=compiler, iterations=args.coremark_iterations if name=='coremark' else 500,
                   original_sources=source_map, adaptations=adaptations, commands=commands,
                   scope='validation and cycle comparison; no certified benchmark score',
                   known_vendor_change=('Ibex removes CoreMark minimum-10-second check; algorithm and CRC checks retained' if name=='coremark' else None),
                   source_hashes={f.name:sha(f) for f in source.iterdir() if f.is_file()},
                   hashes={f:sha(out/f) for f in ('code.elf','code.hex','code.dump')})
        (out/'manifest.json').write_text(json.dumps(row,indent=2)+'\n')
        rows.append(row)
    (args.output/'manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
    print(json.dumps({'output':str(args.output),'applications':len(rows)}))

if __name__ == '__main__':
    main()
