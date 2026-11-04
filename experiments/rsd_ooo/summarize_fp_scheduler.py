#!/usr/bin/env python3
"""Audit same-capacity no-FP scheduler specialization and its FP negative control."""
import argparse
import hashlib
import json
from pathlib import Path
from analyze_fp_domain import analyze
from summarize_scheduler_sweep import audit,load

ROOT=Path(__file__).resolve().parent

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--results-root',type=Path,default=ROOT/'results/fp_scheduler')
    args=p.parse_args()
    rows=[]
    for group in ('diagnostics','applications'):
        data={v:load(args.results_root/v/group,group) for v in ('base','cut')}
        assert set(data['base'])==set(data['cut'])
        assert len(data['base'])==(12 if group=='diagnostics' else 2)
        for name in data['base']:
            original=data['base'][name];candidate=data['cut'][name]
            assert original['input_sha256']==candidate['input_sha256']
            assert original['counters']==candidate['counters']
            assert original['observed_serial']==candidate['observed_serial']
            run_info={}
            for variant,result in (('base',original),('cut',candidate)):
                run=args.results_root/variant/group/name
                audit(run,group,result)
                binary=Path(result['command'][0])
                m=json.loads((binary.parent/'manifest.json').read_text())
                assert m['rob']==64 and m['iq']==m['lq']==m['sq']==16
                assert m['integer_physical_registers']==m['fp_physical_registers']==64 and m['fp_domain_trace']
                assert bool(m['fp_candidate'])==(variant=='cut') and m['candidate'] is None
                assert sha(binary)==m['binary_sha256']
                fp=analyze(run)
                assert not fp['trace_integrity_errors'] and fp['no_fp_dispatch_observed'] and fp['fp_request_issue_replay_pipe_all_zero']
                assert fp['terminal_cycle']==result['counters']['Elapsed cycles']
                run_info[variant]={'binary_sha256':sha(binary),'fp_totals':fp['totals'],
                    'trace_hashes':{f:sha(run/f) for f in ('resource.csv','memory_events.csv','fp_domain.csv','dispatch_events.csv')}}
            assert run_info['base']['trace_hashes']==run_info['cut']['trace_hashes']
            rows.append({'group':group,'name':name,'passed':True,'whole_program_cycles':original['counters']['Elapsed cycles'],
                         'roi_cycles':original.get('roi_cycles'),'input_sha256':original['input_sha256'],
                         'exact_counters_serial_and_four_traces':True,'runs':run_info})
            print(group,name,'paired pass',flush=True)
    negative={}
    for variant in ('base','cut'):
        run=args.results_root/variant/'fp_control/Asm_FP'
        result=json.loads((run/'result.json').read_text())
        fp=analyze(run)
        assert not fp['trace_integrity_errors'] and fp['totals']['fp_scheduler_writes']>0
        if variant=='base':
            audit(run,'upstream',result)
            assert fp['totals']['fp_issue_requests']>0 and fp['totals']['fp_issue']>0
        else:
            assert not result['passed'] and not result['pc_goal_reached']
            assert result['cycles']==result['cycle_limit']-1 and fp['totals']['fp_issue_requests']==0
        negative[variant]={'functional_passed':result['passed'],'pc_goal':result['pc_goal_reached'],
                           'cycles':result['cycles'],'fp_totals':fp['totals'],'result':str(run/'result.json')}
    report={'all_checks_passed':True,'positive_pairs':14,'positive_executions':28,'negative_control_executions':2,
            'proof_instance':{'rob':64,'iq':16,'lq':16,'sq':16,'int_prf':64,'fp_prf':64},
            'scope':'Manual Scheduler.fpIssueReq cut under all actual scheduler.write opType!=FP. Integer/muldiv/memory classes and all capacities retained. Finite full-core evidence plus separate component proof, not full-core equivalence.',
            'rows':rows,'outside_domain_fp_control':negative}
    (args.results_root/'summary.json').write_text(json.dumps(report,indent=2)+'\n')
    print('14 exact positive pairs and FP outside-domain control verified.')

if __name__=='__main__':
    main()
