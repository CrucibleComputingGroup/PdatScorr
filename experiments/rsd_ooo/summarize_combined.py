#!/usr/bin/env python3
"""Audit the same-capacity composition of the LSQ region and no-FP scheduler cuts."""
import argparse
import csv
import hashlib
import json
from pathlib import Path
import re

from analyze_fp_domain import analyze as analyze_fp
from analyze_traces import analyze as analyze_memory
from summarize_scheduler_sweep import audit, load

ROOT = Path(__file__).resolve().parent
TRACES = ('resource.csv', 'memory_events.csv', 'fp_domain.csv', 'dispatch_events.csv')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_build(binary, combined):
    manifest = json.loads((binary.parent/'manifest.json').read_text())
    assert sha(binary) == manifest['binary_sha256']
    assert (manifest['rob'], manifest['iq'], manifest['lq'], manifest['sq'],
            manifest['integer_physical_registers'], manifest['fp_physical_registers'],
            manifest['mshr'], manifest['replay_queue_entries'],
            manifest['fetch_rename_commit_width'], manifest['memory_read_pipeline_depth']) == (64,16,16,16,64,64,2,20,2,5)
    assert manifest['fp_domain_trace'] and not manifest['deep_trace']
    assert bool(manifest['candidate']) == combined
    assert bool(manifest['fp_candidate']) == combined
    assert not manifest.get('prf_reset_guard')
    source = Path(manifest['cwd'])
    for name, digest in manifest['source_sha256'].items():
        assert sha(source/name) == digest, (binary, name, 'source changed after build')
    modules = {'LoadStoreUnit/LoadQueue.sv':'formal/generated/LoadQueue.sv',
               'LoadStoreUnit/StoreQueue.sv':'formal/generated/StoreQueue.sv',
               'Scheduler/Scheduler.sv':'formal/generated_scheduler_nofp/Scheduler.sv'}
    for name, candidate in modules.items():
        expected = ROOT/candidate if combined else ROOT/'rsd/Processor/Src'/name
        assert sha(source/name) == sha(expected), (binary, name)
    return manifest


def check_trace_coverage(run, terminal):
    with (run/'resource.csv').open() as f:
        count = 0
        for count, row in enumerate(csv.DictReader(f), 1):
            assert int(row['cycle']) == count-1
        assert count == terminal+1
    previous = 0
    with (run/'memory_events.csv').open() as f:
        for row in csv.DictReader(f):
            cycle, address, valid = int(row['cycle']), int(row['address']), int(row['reg_valid'])
            assert previous <= cycle <= terminal and 0 <= address < 2**22
            assert valid in (0,1) and row['kind'] in ('load','store')
            previous = cycle


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline', type=Path, default=ROOT/'results/fp_scheduler/base/diagnostics')
    parser.add_argument('--results-root', type=Path, default=ROOT/'results/combined_region_scheduler')
    args = parser.parse_args()
    baseline, combined = load(args.baseline, 'diagnostics'), load(args.results_root/'diagnostics', 'diagnostics')
    expected = {f'{mode}_s{seed}_n512' for mode in ('stream_sum','stream_mix') for seed in (1,7,42)}
    assert set(combined) == expected and expected <= set(baseline)
    rows, builds = [], {}
    for name in sorted(expected):
        pair = {'base':baseline[name], 'combined':combined[name]}
        assert pair['base']['input_sha256'] == pair['combined']['input_sha256']
        assert pair['base']['counters'] == pair['combined']['counters']
        assert pair['base']['observed_serial'] == pair['combined']['observed_serial']
        runs = {}
        for variant, result in pair.items():
            run = (args.baseline if variant == 'base' else args.results_root/'diagnostics')/name
            audit(run, 'diagnostics', result)
            binary = Path(result['command'][0])
            if variant not in builds:
                builds[variant] = check_build(binary, variant == 'combined')
            assert sha(binary) == builds[variant]['binary_sha256'] == result['simulator_sha256']
            raw_counters = {k.strip():float(v) if '.' in v else int(v)
                            for k,v in re.findall(r'^([^\n:]+):\s*([0-9]+(?:\.[0-9]+)?)\s*$', (run/'run.log').read_text(), re.M)}
            assert raw_counters == result['counters']
            terminal = result['counters']['Elapsed cycles']
            check_trace_coverage(run, terminal)
            memory, fp = analyze_memory(run), analyze_fp(run)
            assert memory['region_contract_observed'] and memory['region_contract_violation_count'] == 0
            assert not fp['trace_integrity_errors'] and fp['terminal_cycle'] == terminal
            assert fp['no_fp_dispatch_observed'] and fp['fp_request_issue_replay_pipe_all_zero']
            runs[variant] = {'path':str(run.resolve()), 'cycles':terminal,
                             'code_elf_sha256':sha(run/'code.elf'), 'log_sha256':sha(run/'run.log'),
                             'trace_sha256':{f:sha(run/f) for f in TRACES},
                             'region_contract_observed':True, 'memory_event_counts':memory['memory_event_counts'],
                             'no_fp_dispatch_observed':True, 'fp_totals':fp['totals']}
        assert runs['base']['code_elf_sha256'] == runs['combined']['code_elf_sha256']
        assert runs['base']['trace_sha256'] == runs['combined']['trace_sha256']
        rows.append({'name':name, 'input_sha256':pair['base']['input_sha256'],
                     'exact_counters_serial_and_four_traces':True, 'runs':runs})
        print(name, runs['base']['cycles'], 'exact pair; both contracts observed', flush=True)
    report = {'audit_passed':True, 'positive_pairs':6, 'new_combined_executions':6,
              'reused_baseline_executions':6,
              'scope':'Finite same-capacity composition integration. Each candidate has a separate local proof at this configuration; these six matched executions are not a compositional full-core equivalence proof.',
              'contract_scope':'All logged executeLoad/executeStore physical-address events, including invalid operands and wrong paths; all actual scheduler writes, including wrong paths.',
              'build_manifests':builds, 'rows':rows}
    (args.results_root/'summary.json').write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()
