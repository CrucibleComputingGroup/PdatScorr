#!/usr/bin/env python3
"""Regenerate paired measured comparisons; reject stale inputs or missing checks."""
import argparse
import csv
import hashlib
import json
import re
from pathlib import Path
from rsd_log_checks import assertion_diagnostics

ROOT = Path(__file__).resolve().parent
RESULTS = ROOT/'results'


def read(results, folder, file='summary.json'):
    rows = json.loads((results/folder/file).read_text())
    indexed = {r['name']:r for r in rows}
    assert len(indexed)==len(rows), f'Duplicate case names: {folder}/{file}'
    return indexed


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--results-root', type=Path, default=RESULTS)
    args = parser.parse_args()
    results = args.results_root.resolve()
    names = dict(baseline='kernels_monitored16', queue8='kernels_monitored8',
                 queue4='kernels_monitored4', region_cut='kernels_regioncut16')
    cases = {k:read(results,v) for k,v in names.items()}
    traces = {k:read(results,v,'trace_summary.json') for k,v in names.items()}
    oracle = read(results,'spike_oracle')
    expected = {f'{mode}_s{seed}_n512' for mode in
                ('stream_sum','stream_mix','pointer_chase','alias_feedback') for seed in (1,7,42)}
    for group in [oracle,*cases.values(),*traces.values()]:
        assert set(group)==expected, 'Missing or unexpected experimental cases'
    rows = []
    for name, base in cases['baseline'].items():
        assert oracle[name]['status']=='passed'
        assert oracle[name]['input_sha256']==base['input_sha256']
        oracle_dir = results/'spike_oracle'/name
        assert json.loads((oracle_dir/'result.json').read_text())==oracle[name]
        assert sha(oracle_dir/'run.log')==oracle[name]['log_sha256']
        assert sha(oracle_dir/'code.hex')==oracle[name]['input_sha256']
        for variant, data in cases.items():
            r = data[name]
            trace = traces[variant][name]
            run_dir = results/names[variant]/name
            assert json.loads((run_dir/'result.json').read_text())==r, 'Stale aggregate result'
            assert sha(run_dir/'code.hex')==r['input_sha256']
            assert sha(run_dir/'code.elf')==sha(oracle_dir/'code.elf'), 'Different RTL/Spike ELF'
            assert sha(run_dir/'run.log')==r['log_sha256']
            assert sha(Path(r['simulator']))==r['simulator_sha256']
            log = (run_dir/'run.log').read_text()
            serial = (run_dir/'serial.out.txt').read_text()
            assert r['returncode']==0 and r['pc_goal'] and r['within_cycle_limit']
            assert 'PC reached PC_GOAL:' in log
            assert not re.search(r'Assertion failed|%Error|Exception caused',log)
            assert not assertion_diagnostics(log), 'Named RSD assertion diagnostic in raw log'
            assert re.findall(r'^Elapsed cycles:\s*(\d+)$',log,re.M)==[str(r['counters']['Elapsed cycles'])]
            assert serial==r['observed_serial']
            assert (serial==r['expected_serial'])==r['serial_match']
            assert set(trace['trace_sha256'])=={'resource.csv','memory_events.csv'}
            for filename, digest in trace['trace_sha256'].items():
                assert sha(run_dir/filename)==digest, 'Stale trace analysis'
            assert base['input_sha256']==r['input_sha256'], 'Different binaries in paired comparison'
            if variant!='region_cut':
                assert r['status']=='passed' and r['serial_match']
            else:
                if r['mode'] in ('stream_sum','stream_mix'):
                    assert trace['region_contract_observed'], 'Positive stream case violates its contract'
                if trace['region_contract_observed']:
                    assert r['status']=='passed' and r['serial_match']
                    assert base['counters']==r['counters']
                    assert traces['baseline'][name]['region_contract_observed']
                if r['mode']=='alias_feedback':
                    assert r['status']=='failed' and not r['serial_match']
                if r['mode']=='pointer_chase':
                    assert r['status']=='passed' and r['serial_match']
                    assert not trace['region_contract_observed']
            memory_equal = ((results/names[variant]/name/'memory_events.csv').read_bytes()
                == (results/names['baseline']/name/'memory_events.csv').read_bytes())
            resource_equal = ((results/names[variant]/name/'resource.csv').read_bytes()
                == (results/names['baseline']/name/'resource.csv').read_bytes())
            if variant=='region_cut' and trace['region_contract_observed']:
                assert memory_equal and resource_equal
            rows.append(dict(workload=name, mode=r['mode'], seed=r['seed'], variant=variant,
                status=r['status'], cycles=r['counters']['Elapsed cycles'],
                cycle_ratio=r['counters']['Elapsed cycles']/base['counters']['Elapsed cycles'],
                region_contract_observed=trace['region_contract_observed'],
                region_violations=trace['region_contract_violation_count'],
                exact_memory_event_trace=memory_equal, exact_resource_trace=resource_equal,
                max_lq=trace['max_occupancy']['lq'], max_sq=trace['max_occupancy']['sq'],
                max_mshr=trace['max_occupancy']['mshr'],
                source_result=str(results/names[variant]/name/'result.json')))
    report = dict(status='validated',
        scope='12 deterministic diagnostic kernels per variant, three seeds for four algorithms; simulator-reported cycle counts include software startup and serial output. Region cut positive claims only for six streaming cases satisfying every sampled speculative execute-event contract. Queue tuning is not cycle equivalence. No observed occupancy is an all-input bound.',
        rows=rows)
    output = results/'experiment_summary.json'
    output.write_text(json.dumps(report,indent=2)+'\n')
    with (results/'experiment_comparison.csv').open('w') as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0]))
        w.writeheader()
        w.writerows(rows)
    print(json.dumps({'status':report['status'],'comparisons':len(rows),
        'region_positive_cases':sum(r['variant']=='region_cut' and r['region_contract_observed'] for r in rows),
        'expected_negative_failures':sum(r['variant']=='region_cut' and r['status']=='failed' for r in rows),
        'summary':str(output),'summary_sha256':hashlib.sha256(output.read_bytes()).hexdigest()}))


if __name__ == '__main__':
    main()
