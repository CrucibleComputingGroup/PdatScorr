#!/usr/bin/env python3
"""Recompute the measured 5/10/20-stage read-response pipeline experiment."""
import csv
import argparse
import hashlib
import json
from pathlib import Path
import re
from analyze_lifetimes import analyze as lifetimes
from analyze_traces import analyze as resources

ROOT=Path(__file__).resolve().parent
RESULTS=ROOT/'results'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--results-root',type=Path,default=RESULTS,
                   help='Root containing latency_{base,cut}_p{5,10,20} run directories')
    args=p.parse_args()
    results_root=args.results_root
    rows=[]
    pairs=[]
    expected={f'{mode}_s{seed}_n512' for mode in ('stream_sum','stream_mix') for seed in (1,7,42)}
    program_hashes={}
    checked_builds=set()
    for depth in [5,10,20]:
        by_variant={}
        for variant in ['base','cut']:
            run_root=results_root/f'latency_{variant}_p{depth}'
            results=json.loads((run_root/'summary.json').read_text())
            assert len(results)==6 and {r['name'] for r in results}==expected, 'Wrong case set'
            by_variant[variant]={}
            for result in results:
                run=run_root/result['name']
                assert json.loads((run/'result.json').read_text())==result, 'Stale aggregate result'
                assert sha(run/'code.hex')==result['input_sha256'], 'Stale program image'
                assert sha(run/'run.log')==result['log_sha256'], 'Stale raw log'
                program_hashes.setdefault(result['name'],result['input_sha256'])
                assert program_hashes[result['name']]==result['input_sha256'], 'Different input images'
                log=(run/'run.log').read_text(errors='replace')
                assert 'PC reached PC_GOAL:' in log and not re.search(r'Assertion failed|%Error|Exception caused',log)
                assert re.findall(r'^Elapsed cycles:\s*(\d+)$',log,re.M)==[str(result['counters']['Elapsed cycles'])]
                assert (run/'serial.out.txt').read_bytes()==result['expected_serial'].encode(), 'Wrong architectural signature'
                binary=Path(result['simulator'])
                manifest=json.loads((binary.parent/'manifest.json').read_text())
                assert manifest['lq']==manifest['sq']==16 and manifest['memory_read_pipeline_depth']==depth
                assert manifest['deep_trace'] and bool(manifest['candidate'])==(variant=='cut')
                assert manifest['binary_sha256']==result['simulator_sha256']
                if binary not in checked_builds:
                    assert sha(binary)==manifest['binary_sha256'], 'Stale simulator'
                    for filename,digest in manifest['source_sha256'].items():
                        assert sha(Path(manifest['cwd'])/filename)==digest, 'Stale build source'
                    checked_builds.add(binary)
                life=lifetimes(run)
                resource=resources(run)
                assert resource['resource_samples']==result['counters']['Elapsed cycles']+1
                assert life['mshr_first_cycle']==0 and life['mshr_last_cycle']==result['counters']['Elapsed cycles']
                assert set(life['mshr_slot_samples'])=={0,1}
                assert all(n==resource['resource_samples'] for n in life['mshr_slot_samples'].values())
                row={'variant':variant,'read_pipeline_stages':depth,'name':result['name'],
                     'status':result['status'],'cycles':result['counters']['Elapsed cycles'],
                     'instructions':result['counters']['Num of committed RISC-V-ops'],
                     'max_mshr_occupancy':resource['max_occupancy']['mshr'],
                     'multiple_misses_samples':resource['multiple_misses_samples'],
                     'mshr_complete_intervals':life['mshr_lifetime_cycles']['count'],
                     'mshr_lifetime_max':life['mshr_lifetime_cycles']['max'],
                     'mshr_lifetime_mean':life['mshr_lifetime_cycles']['mean'],
                     'backing_read_max':life['backing_read_latency_cycles']['max'],
                     'backing_read_mean':life['backing_read_latency_cycles']['mean'],
                     'backing_min_observed_read_request_gap':life['backing_min_observed_read_request_gap'],
                     'mshr_censored_intervals':len(life['mshr_censored_intervals']),
                     'backing_pending_reads_at_end':sum(len(v) for v in life['backing_pending_at_end'].values()),
                     'input_sha256':result['input_sha256'],
                     'simulator_sha256':result['simulator_sha256'],
                     'isa_disallowed_samples':life['isa_disallowed_samples'],
                     'region_violations':resource['region_contract_violation_count'],
                     'trace_integrity_ok':not (life['trace_integrity_errors'] or life['backing_unmatched_responses']
                       or life['backing_serial_reuse_while_pending'] or life['isa_monitor_recompute_mismatches']),
                     'raw_result':str(run/'result.json')}
                rows.append(row)
                by_variant[variant][result['name']]=row
        assert set(by_variant['base'])==set(by_variant['cut'])
        for name,base in by_variant['base'].items():
            cut=by_variant['cut'][name]
            a=results_root/f'latency_base_p{depth}'/name
            b=results_root/f'latency_cut_p{depth}'/name
            pair={'read_pipeline_stages':depth,'name':name,
                  'same_program_image':base['input_sha256']==cut['input_sha256'],
                  'same_cycles':base['cycles']==cut['cycles'],
                  'same_instructions':base['instructions']==cut['instructions'],
                  'same_serial_output':sha(a/'serial.out.txt')==sha(b/'serial.out.txt'),
                  'identical_traces':{f:sha(a/f)==sha(b/f) for f in ['resource.csv','memory_events.csv','predecode.csv','mshr.csv','backing_memory.csv']}}
            pairs.append(pair)
    summary={'scope':'Finite full-core RTL executions; same program images and initial state within each paired latency setting. No universal latency or occupancy bound.',
             'setting':'MemoryTypes.MEMORY_READ_PIPELINE_DEPTH=5/10/20. Read/write busy-count parameters2 (minimum accepted-request gap3 cycles), jitter modulo10, seed1987534242, LQ/SQ16, MSHR2 held fixed.',
             'edge_convention':life['edge_convention'],
             'cycle_convention':'The upstream harness reports zero-based terminal cycle N; resource/MSHR traces contain N+1 post-rising-edge samples from0 throughN. Cycle differences use the same sample origin.',
             'rows':rows,'pairs':pairs,
             'all_checks_passed':len(rows)==36 and all(r['status']=='passed' and r['trace_integrity_ok']
                 and r['isa_disallowed_samples']==0 and r['region_violations']==0 and r['mshr_complete_intervals']>0 for r in rows)
                 and all(p['same_program_image'] and p['same_cycles'] and p['same_instructions'] and p['same_serial_output'] and all(p['identical_traces'].values()) for p in pairs)}
    (results_root/'latency_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    with (results_root/'latency_summary.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=rows[0]);writer.writeheader();writer.writerows(rows)
    print('36 runs / 18 matched pairs verified:',summary['all_checks_passed'])
    for r in rows:
        if r['variant']=='base':
            print(r['name'],r['read_pipeline_stages'],r['cycles'],r['backing_read_max'],r['mshr_lifetime_max'])
    return 0 if summary['all_checks_passed'] else 1

if __name__=='__main__':
    raise SystemExit(main())
