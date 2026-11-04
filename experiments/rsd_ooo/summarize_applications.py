#!/usr/bin/env python3
"""Audit the six completed application runs and compare measured ROI cycles."""
import csv
import argparse
import hashlib
import json
from pathlib import Path
import re
from run_applications import validate

ROOT = Path(__file__).resolve().parent

def normalized_serial(name, serial):
    timing = (r'^(?:Total ticks|Total time \(secs\)|Iterations/Sec)\s*:.*\n' if name=='coremark'
              else r'^(?:ROI cycles|Microseconds for one run through Dhrystone|Dhrystones per Second)\s*:.*\n')
    return re.sub(timing,'',serial,flags=re.M)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--results-root',type=Path,default=ROOT/'results')
    p.add_argument('--output',type=Path)
    args=p.parse_args()
    grouped = {}
    checks = {}
    for size in (16,8,4):
        path = args.results_root/f'apps_lq{size}_sq{size}/summary.json'
        raw_rows=json.loads(path.read_text())
        grouped[size] = {r['name']:r for r in raw_rows}
        checks[f'size{size}_two_passes'] = len(raw_rows)==2 and set(grouped[size])=={'coremark','dhrystone'} and all(r['status']=='passed' for r in grouped[size].values())
        for name,row in grouped[size].items():
            run = path.parent/name
            checks[f'{name}_{size}_result_agrees'] = json.loads((run/'result.json').read_text())==row
            checks[f'{name}_{size}_actual_input_hash'] = hashlib.sha256((run/'code.hex').read_bytes()).hexdigest()==row['input_sha256']
            binary=Path(row['command'][0])
            manifest=json.loads((binary.parent/'manifest.json').read_text())
            checks[f'{name}_{size}_actual_binary_hash'] = hashlib.sha256(binary.read_bytes()).hexdigest()==row['binary_sha256']==manifest['binary_sha256']
            checks[f'{name}_{size}_actual_capacity'] = manifest['lq']==manifest['sq']==size
            checks[f'{name}_{size}_raw_serial_hash'] = hashlib.sha256((run/'serial.out.txt').read_bytes()).hexdigest()==row['serial_sha256']
            serial=(run/'serial.out.txt').read_text()
            validation,roi=validate(name,serial,row['iterations'])
            checks[f'{name}_{size}_raw_validation'] = all(validation.values()) and roi==row['roi_cycles'] and serial==row['observed_serial']
            log=(run/'run.log').read_text(errors='replace')
            checks[f'{name}_{size}_raw_log'] = ('PC reached PC_GOAL:' in log and
                not re.search(r'Assertion failed|%Error|Exception caused',log) and
                re.findall(r'^Elapsed cycles:\s*(\d+)$',log,re.M)==[str(row['counters']['Elapsed cycles'])])
    rows = []
    for name in ('coremark','dhrystone'):
        base = grouped[16][name]
        for size in (16,8,4):
            row = grouped[size][name]
            checks[f'{name}_{size}_same_input'] = row['input_sha256']==base['input_sha256']
            checks[f'{name}_{size}_same_nontiming_serial'] = normalized_serial(name,row['observed_serial'])==normalized_serial(name,base['observed_serial'])
            rows.append(dict(application=name,iterations=row['iterations'],lq=size,sq=size,
                             status=row['status'],roi_cycles=row['roi_cycles'],
                             roi_ratio_vs16=row['roi_cycles']/base['roi_cycles'],
                             whole_program_cycles=row['counters']['Elapsed cycles'],
                             binary_sha256=row['binary_sha256'],input_sha256=row['input_sha256']))
    summary = dict(all_checks_passed=all(checks.values()),checks=checks,rows=rows,
                   scope='RV32IM application capacity tuning only. Outside no-M ISA and nonalias-region contracts. No certified scores.',
                   timing='Actual mcycle deltas around upstream benchmark loops; whole-program cycles separately include startup and UART reporting.')
    out = args.output or args.results_root/'application_summary.json'
    out.write_text(json.dumps(summary,indent=2)+'\n')
    with out.with_suffix('.csv').open('w') as f:
        w = csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
    print(json.dumps(summary,indent=2))
    if not summary['all_checks_passed']:
        raise SystemExit(1)

if __name__=='__main__':
    main()
