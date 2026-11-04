#!/usr/bin/env python3
"""Audit the FLW/FSW-only boundary of the no-FP-arithmetic Scheduler cut."""
import argparse
import hashlib
import json
from pathlib import Path
import re

from analyze_fp_domain import analyze
from rsd_log_checks import assertion_diagnostics

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--results-root', type=Path, default=ROOT/'results/fp_memory')
    parser.add_argument('--workloads', type=Path, default=ROOT/'fp_memory_workloads')
    args = parser.parse_args()
    root = args.results_root.resolve()
    specs = json.loads((args.workloads/'manifest.json').read_text())
    expected = {f'fp_memory_only_s{s}_n128' for s in (1,7,42)}
    assert {x['name'] for x in specs} == expected and len(specs) == 3
    datasets = {}
    for variant in ('spike','baseline','scheduler_cut'):
        data = json.loads((root/variant/'summary.json').read_text())
        assert len(data) == 3 and {x['name'] for x in data} == expected
        datasets[variant] = {x['name']:x for x in data}
    rows = []
    traces = ('resource.csv','memory_events.csv','fp_domain.csv','dispatch_events.csv')
    for spec in specs:
        name = spec['name']
        source = args.workloads/name
        for filename, digest in spec['hashes'].items():
            assert sha(source/filename) == digest
        words = [int(x,16) for x in re.findall(r'^\.word 0x([0-9a-f]+)$',
                                               (source/'code.S').read_text(),re.M)]
        assert len(words) == 256
        signature = sum(((a+b)&0xffffffff) for a,b in zip(words[:128],words[128:])) & 0xffffffff
        assert spec['expected_serial'] == f'signature={signature:08x}\n'
        domains = {}
        for variant in datasets:
            result = datasets[variant][name]
            run = root/variant/name
            assert json.loads((run/'result.json').read_text()) == result
            assert result['status'] == 'passed' and result['returncode'] == 0
            assert sha(run/'code.hex') == result['input_sha256'] == spec['hashes']['code.hex']
            assert sha(run/'code.elf') == spec['hashes']['code.elf']
            assert sha(run/'run.log') == result['log_sha256']
            assert sha(Path(result['simulator'])) == result['simulator_sha256']
            log = (run/'run.log').read_text()
            if variant == 'spike':
                assert '--isa=rv32imf_zicsr' in result['command']
                assert result['checksum_match']
                assert re.findall(r'^0x([0-9a-fA-F]+)\s*$',log,re.M) == [f'{signature:08x}']
                continue
            assert result['pc_goal'] and result['within_cycle_limit'] and result['serial_match']
            assert 'PC reached PC_GOAL:' in log
            assert not assertion_diagnostics(log)
            assert not re.search(r'Assertion failed|%Error|Exception caused',log)
            assert (run/'serial.out.txt').read_text() == spec['expected_serial']
            assert re.findall(r'^Elapsed cycles:\s*(\d+)$',log,re.M) == [str(result['counters']['Elapsed cycles'])]
            domain = analyze(run)
            assert not domain['trace_integrity_errors']
            assert domain['no_fp_dispatch_observed'] and domain['fp_request_issue_replay_pipe_all_zero']
            assert domain['sample_count'] == result['counters']['Elapsed cycles']+1
            # RSD TestMain dumps x0..x31, PC, then f0..f31.
            registers = [int(x,16) for x in (run/'reg.out.hex').read_text().split()]
            assert len(registers) == 65
            assert registers[33] == words[127] and registers[64] == words[255]
            domains[variant] = domain
        base, cut = datasets['baseline'][name], datasets['scheduler_cut'][name]
        assert base['counters'] == cut['counters']
        equal = {f:sha(root/'baseline'/name/f) == sha(root/'scheduler_cut'/name/f) for f in traces}
        assert all(equal.values())
        rows.append(dict(name=name, cycles=base['counters']['Elapsed cycles'],
                         signature=spec['expected_serial'].strip(), exact_traces=equal,
                         no_fp_arithmetic_dispatch=True, final_f0=f'{words[127]:08x}',
                         final_f31=f'{words[255]:08x}', source_result=str(root/'baseline'/name/'result.json')))
    report = dict(status='validated',
        scope='Three FP-memory-only input pairs plus independent Spike. FLW/FSW use the retained FP register file but dispatch as memory operations; the Scheduler cut excludes FP arithmetic requests, not all FP-register activity. Finite observations, not all-input adherence or whole-core equivalence.',
        rows=rows)
    (root/'summary.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
