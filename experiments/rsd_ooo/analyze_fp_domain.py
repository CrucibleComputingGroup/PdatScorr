#!/usr/bin/env python3
"""Check actual scheduler writes and the FP issue/replay consumer chain."""
import argparse
import collections
import csv
import hashlib
import json
from pathlib import Path

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def analyze(run):
    totals=collections.Counter()
    types=collections.Counter()
    errors=[]
    first_bad=[]
    previous=None
    with (run/'dispatch_events.csv').open() as dispatch_file, (run/'fp_domain.csv').open() as fp_file:
        events=iter(csv.DictReader(dispatch_file))
        event=next(events,None)
        samples=0
        for row in csv.DictReader(fp_file):
            r={k:int(v) for k,v in row.items()}
            cycle=r.pop('cycle')
            if (previous is None and cycle!=0) or (previous is not None and cycle!=previous+1):
                errors.append({'kind':'nonconsecutive_cycle','cycle':cycle})
            previous=cycle
            samples+=1
            writes=fp_writes=0
            while event is not None and int(event['cycle'])<=cycle:
                if int(event['cycle'])!=cycle:
                    errors.append({'kind':'dispatch_cycle_mismatch','event':event})
                op=int(event['op_type']); types[op]+=1; writes+=1; fp_writes+=op==3
                event=next(events,None)
            if (writes,fp_writes)!=(r['scheduler_writes'],r['fp_scheduler_writes']):
                errors.append({'kind':'dispatch_count_mismatch','cycle':cycle})
            totals.update(r)
            if any(r[k] for k in r if k!='scheduler_writes') and len(first_bad)<20:
                first_bad.append({'cycle':cycle,**r})
        if event is not None:
            errors.append({'kind':'unconsumed_dispatch_event','event':event})
    result={'scope':'Finite post-rising-edge samples of actual scheduler.write events including wrong-path operations; no all-input program-contract claim.',
            'contract':'Every scheduler.write implies typed SchedulerEntry.opType != MOP_TYPE_FP(3).',
            'sample_count':samples,'terminal_cycle':previous,'totals':dict(totals),'dispatch_op_types':dict(types),
            'no_fp_dispatch_observed':totals['scheduler_writes']>0 and totals['fp_scheduler_writes']==0,
            'fp_request_issue_replay_pipe_all_zero':all(totals[k]==0 for k in totals if k not in ('scheduler_writes','fp_scheduler_writes')),
            'first_fp_events':first_bad,'trace_integrity_errors':errors,
            'trace_sha256':{f:sha(run/f) for f in ('fp_domain.csv','dispatch_events.csv')}}
    (run/'fp_domain_summary.json').write_text(json.dumps(result,indent=2)+'\n')
    return result

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('directories',type=Path,nargs='+')
    args=p.parse_args()
    ok=True
    for directory in args.directories:
        r=analyze(directory)
        print(directory,r['totals'],len(r['trace_integrity_errors']))
        ok &= not r['trace_integrity_errors']
    return 0 if ok else 1

if __name__=='__main__':
    raise SystemExit(main())
