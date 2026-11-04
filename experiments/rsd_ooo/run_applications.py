#!/usr/bin/env python3
"""Run RSD applications, retaining raw logs and checking original validation data."""
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

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def validate(name, text, iterations):
    checks = {}
    if name == 'coremark':
        expected = {'seedcrc':'18f2', 'crclist':'e3c1', 'crcmatrix':'0747', 'crcstate':'8d84'}
        for field, value in expected.items():
            found = re.findall(r'(?:\[0\])?'+field+r'\s*:\s*0x([0-9a-f]+)', text)
            checks[field] = len(found)==1 and int(found[0],16)==int(value,16)
        checks['validated'] = 'Correct operation validated.' in text
        checks['iterations'] = re.findall(r'Iterations\s*:\s*(\d+)',text)==[str(iterations)]
        checks['data_size'] = re.findall(r'CoreMark Size\s*:\s*(\d+)',text)==['666']
        checks['no_errors'] = not re.search(r'ERROR|Errors detected|Cannot validate',text)
        m = re.search(r'Total ticks\s*:\s*(\d+)',text)
    else:
        # Values explicitly specified beside the original benchmark prints.
        expected = {'Int_Glob':'5','Bool_Glob':'1','Ch_1_Glob':'A','Ch_2_Glob':'B',
                    'Arr_1_Glob[8]':'7','Arr_2_Glob[8][7]':str(iterations+10),
                    'Int_1_Loc':'5','Int_2_Loc':'13','Int_3_Loc':'7','Enum_Loc':'1',
                    'Str_1_Loc':"DHRYSTONE PROGRAM, 1'ST STRING",
                    'Str_2_Loc':"DHRYSTONE PROGRAM, 2'ND STRING"}
        for field, value in expected.items():
            checks[field] = re.findall(r'^'+re.escape(field)+r':\s*([^\n]+)',text,re.M)==[value]
        for field, values in {'Discr':['0','0'],'Enum_Comp':['2','1'],'Int_Comp':['17','18'],
                              'Str_Comp':['DHRYSTONE PROGRAM, SOME STRING']*2}.items():
            checks[field] = re.findall(r'^  '+field+r':\s*([^\n]+)',text,re.M)==values
        ptrs = re.findall(r'^  Ptr_Comp:\s*(-?\d+)',text,re.M)
        checks['pointer_relation'] = len(ptrs)==2 and ptrs[0]==ptrs[1]
        checks['iterations'] = re.findall(r'Trying (\d+) runs',text)==[str(iterations)]
        m = re.search(r'ROI cycles:\s*(\d+)',text)
    checks['positive_roi_cycles'] = bool(m and int(m[1])>0)
    return checks, int(m[1]) if m else None

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--binary',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--applications',type=Path,default=ROOT/'applications')
    p.add_argument('--max-cycles',type=int,default=20000000)
    p.add_argument('--timeout',type=int,default=600)
    args = p.parse_args()
    args.output.mkdir(parents=True,exist_ok=False)
    binary = args.binary.resolve()
    rows = []
    for spec in json.loads((args.applications/'manifest.json').read_text()):
        run = args.output.resolve()/spec['name']
        run.mkdir()
        for f in ('code.hex','code.elf','manifest.json'):
            shutil.copy2(args.applications/spec['name']/f,run/f)
        cmd = [str(binary),f'TEST_CODE={run}',f'MAX_TEST_CYCLES={args.max_cycles}',
               'ENABLE_PC_GOAL=1','SHOW_SERIAL_OUT=1']
        row = dict(name=spec['name'],command=cmd,binary_sha256=sha(binary),
                   input_sha256=sha(run/'code.hex'),iterations=spec['iterations'],status='failed',
                   scope='original algorithm checks and PC-goal; validation cycle comparison, no score certification')
        start = time.monotonic()
        try:
            result = subprocess.run(cmd,cwd=run,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,
                                    env=dict(os.environ,PATH='/usr/bin:/bin:/usr/local/bin'),timeout=args.timeout)
            raw = result.stdout
            row['returncode'] = result.returncode
        except subprocess.TimeoutExpired as exc:
            raw = exc.stdout or b''
            row['status'] = 'timeout'
        (run/'run.log').write_bytes(raw)
        row['log_sha256'] = hashlib.sha256(raw).hexdigest()
        log = raw.decode(errors='replace')
        row['named_rsd_assertion_diagnostics'] = assertion_diagnostics(log)
        row['wall_seconds'] = time.monotonic()-start
        row['pc_goal'] = 'PC reached PC_GOAL:' in log
        serial = (run/'serial.out.txt').read_bytes() if (run/'serial.out.txt').exists() else b''
        row['serial_sha256'] = hashlib.sha256(serial).hexdigest()
        row['observed_serial'] = serial.decode(errors='replace')
        row['validation'],row['roi_cycles'] = validate(spec['name'],row['observed_serial'],spec['iterations'])
        row['counters'] = {k.strip():float(v) if '.' in v else int(v)
                           for k,v in re.findall(r'^([^\n:]+):\s*([0-9]+(?:\.[0-9]+)?)\s*$',log,re.M)}
        cycles = row['counters'].get('Elapsed cycles')
        row['within_cycle_limit'] = cycles is not None and cycles < args.max_cycles-1
        if (row.get('returncode')==0 and row['pc_goal'] and row['within_cycle_limit'] and
            all(row['validation'].values()) and not row['named_rsd_assertion_diagnostics'] and
            not re.search(r'Assertion failed|%Error|Exception caused',log)):
            row['status'] = 'passed'
        (run/'result.json').write_text(json.dumps(row,indent=2)+'\n')
        rows.append(row)
        (args.output/'summary.json').write_text(json.dumps(rows,indent=2)+'\n')
        print(json.dumps({k:row[k] for k in ('name','status','roi_cycles','wall_seconds')}),flush=True)
    if any(r['status']!='passed' for r in rows):
        raise SystemExit(1)

if __name__ == '__main__':
    main()
