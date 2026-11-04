#!/usr/bin/env python3
"""Run RSD RTL or Spike on generated kernels, preserving logs and failures."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time
from rsd_log_checks import assertion_diagnostics

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--simulator', type=Path, required=True)
    p.add_argument('--spike', action='store_true')
    p.add_argument('--spike-isa', default='rv32im_zicsr',
                   help='ISA used only by Spike; retained integer experiments use the default')
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--workloads', type=Path, default=ROOT/'workloads')
    p.add_argument('--filter', default='')
    p.add_argument('--max-cycles', type=int, default=1000000)
    p.add_argument('--timeout', type=int, default=120)
    args = p.parse_args()
    sim = args.simulator.resolve()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    rows = []
    env = dict(os.environ, PATH='/usr/bin:/bin:/usr/local/bin')
    for spec in json.loads((args.workloads/'manifest.json').read_text()):
        if args.filter not in spec['name']:
            continue
        run = out/spec['name']
        # Avoid stale output being interpreted as a new successful run.
        if run.exists():
            raise RuntimeError(f'Output exists; use a fresh run directory: {run}')
        run.mkdir()
        image = args.workloads/spec['name']
        for name in ('code.hex','code.elf','manifest.json'):
            shutil.copy2(image/name, run/name)
        if args.spike:
            (run/'debug.cmd').write_text('until pc 0 1004\nreg 0 s4\nquit\n')
            cmd = [str(sim), '--isa='+args.spike_isa, '--priv=m', '--pc=0x1000',
                   '--disable-dtb', '-m0x1000:0xf000,0x80000000:0x40000,0x40002000:0x1000',
                   '-d', '--debug-cmd='+str(run/'debug.cmd'), str(run/'code.elf')]
        else:
            cmd = [str(sim), f'TEST_CODE={run}', f'MAX_TEST_CYCLES={args.max_cycles}',
                   'ENABLE_PC_GOAL=1', 'SHOW_SERIAL_OUT=1']
        row = dict(name=spec['name'], mode=spec['mode'], seed=spec['seed'],
                   region_contract=spec['region_contract'], simulator=str(sim),
                   simulator_sha256=sha(sim), input_sha256=sha(run/'code.hex'),
                   command=cmd, expected_serial=spec['expected_serial'], status='failed')
        start = time.monotonic()
        try:
            result = subprocess.run(cmd, cwd=run, env=env, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, timeout=args.timeout)
            log = result.stdout.decode(errors='replace')
            row['returncode'] = result.returncode
            if args.spike:
                observed = re.findall(r'^0x([0-9a-fA-F]+)\s*$', log, re.M)
                expected = int(spec['expected_serial'].split('=')[1], 16)
                row['checksum_match'] = len(observed)==1 and int(observed[0],16)==expected
                row['status'] = 'passed' if result.returncode==0 and row['checksum_match'] else 'failed'
                row['verification_scope'] = 'Spike reaches exact PC 0x1004 and x20 matches independent arithmetic oracle'
            else:
                serial = (run/'serial.out.txt').read_text() if (run/'serial.out.txt').exists() else None
                row['observed_serial'] = serial
                row['serial_match'] = serial == spec['expected_serial']
                row['pc_goal'] = 'PC reached PC_GOAL:' in log
                # All numeric summary fields from the harness, including instrumentation.
                row['counters'] = {k.strip():float(v) if '.' in v else int(v)
                                   for k,v in re.findall(r'^([^\n:]+):\s*([0-9]+(?:\.[0-9]+)?)\s*$', log, re.M)}
                cycles = row['counters'].get('Elapsed cycles')
                row['within_cycle_limit'] = cycles is not None and cycles < args.max_cycles-1
                row['named_rsd_diagnostics'] = assertion_diagnostics(log)
                row['status'] = 'passed' if (result.returncode==0 and row['pc_goal'] and
                    row['serial_match'] and row['within_cycle_limit'] and
                    not row['named_rsd_diagnostics'] and
                    not re.search(r'Assertion failed|%Error|Exception caused',log)) else 'failed'
                row['verification_scope'] = 'RTL PC-goal, exact serial checksum, timeout and identifiable named RSD/runtime diagnostics; empty-message assertions are not identifiable from these logs; no full equivalence claim'
        except subprocess.TimeoutExpired as exc:
            log = (exc.stdout or b'').decode(errors='replace')
            row['status'] = 'timeout'
        row['wall_seconds'] = time.monotonic()-start
        (run/'run.log').write_text(log)
        row['log_sha256'] = sha(run/'run.log')
        (run/'result.json').write_text(json.dumps(row,indent=2)+'\n')
        rows.append(row)
        (out/'summary.json').write_text(json.dumps(rows,indent=2)+'\n')
        print(json.dumps({k:row[k] for k in ('name','status','wall_seconds')}),flush=True)
    if not rows:
        raise RuntimeError('No workloads selected')
    if any(r['status']!='passed' for r in rows):
        raise SystemExit(1)


if __name__ == '__main__':
    main()
