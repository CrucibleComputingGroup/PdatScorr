#!/usr/bin/env python3
"""Run upstream, diagnostic and application checks for one isolated capacity build."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parent

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--binary',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args()
    args.output.mkdir(parents=True,exist_ok=False)
    binary=args.binary.resolve()
    commands=[('upstream',[sys.executable,str(ROOT/'run_upstream_tests.py'),'--binary',str(binary),
                           '--output',str(args.output/'upstream')]),
              ('diagnostics',[sys.executable,str(ROOT/'run_workloads.py'),'--simulator',str(binary),
                              '--output',str(args.output/'diagnostics')]),
              ('applications',[sys.executable,str(ROOT/'run_applications.py'),'--binary',str(binary),
                               '--output',str(args.output/'applications')])]
    report={'binary':str(binary),'configuration':json.loads((binary.parent/'manifest.json').read_text()),'groups':[]}
    for name,cmd in commands:
        start=time.monotonic()
        with (args.output/(name+'_runner.log')).open('w') as log:
            run=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,
                               env=dict(os.environ,PATH='/usr/bin:/bin:/usr/local/bin'))
        report['groups'].append({'name':name,'command':cmd,'returncode':run.returncode,
                                 'wall_seconds':time.monotonic()-start})
        report['passed']=all(r['returncode']==0 for r in report['groups'])
        (args.output/'suite.json').write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps(report['groups'][-1]),flush=True)
    return 0 if report['passed'] else 1

if __name__=='__main__':
    raise SystemExit(main())
