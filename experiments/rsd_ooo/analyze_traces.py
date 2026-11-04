#!/usr/bin/env python3
"""Summarize measured occupancy and check every logged speculative memory event.

No observed maximum is reported as a formal resource bound. CSV samples are
post-rising-edge occupancies plus next-edge combinational event signals.
"""
import argparse
from collections import Counter
import csv
import hashlib
import json
from pathlib import Path


def analyze(run):
    result = json.loads((run/'result.json').read_text())
    stats = {'name':result['name'], 'rtl_status':result['status'],
             'region_contract_requested':result['region_contract'],
             'cycles':result.get('counters',{}).get('Elapsed cycles')}
    stats['trace_sha256'] = {p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                            for p in (run/'resource.csv',run/'memory_events.csv') if p.exists()}
    resources = run/'resource.csv'
    memory = run/'memory_events.csv'
    if resources.exists():
        with resources.open() as f:
            rows = [{k:int(v) for k,v in row.items()} for row in csv.DictReader(f)]
        if not rows:
            raise RuntimeError(f'Empty resource trace: {resources}')
        stats['resource_samples'] = len(rows)
        stats['occupancy_histograms'] = {
            k: dict(sorted(Counter(r[k] for r in rows).items()))
            for k in ('lq','sq','rob','iq','mshr')}
        stats['max_occupancy'] = {k:max(r[k] for r in rows) for k in ('lq','sq','rob','iq','mshr')}
        stats['sampled_not_allocatable_cycles'] = {
            k:sum(r[k] for r in rows) for k in ('lq_not_allocatable','sq_not_allocatable','rename_stall')}
        stats['multiple_misses_samples'] = sum(r['mshr']>1 for r in rows)
        stats['recovery_samples'] = sum(r['recovery'] for r in rows)
    if memory.exists():
        violations = []
        counts = Counter()
        with memory.open() as f:
            for row in csv.DictReader(f):
                address, valid = int(row['address']), int(row['reg_valid'])
                counts[row['kind']] += 1
                counts[row['kind']+'_invalid_operand'] += not valid
                good = address >> 16 == 0 if row['kind']=='load' else address >> 16 != 0
                if not good:
                    violations.append(dict(row, address_hex=f'0x{address:06x}'))
        stats['memory_event_counts'] = dict(counts)
        stats['region_contract_violation_count'] = len(violations)
        stats['first_region_contract_violations'] = violations[:10]
        stats['region_contract_observed'] = not violations and counts['load']>0 and counts['store']>0
    stats['scope'] = 'Finite sampled RTL executions, including invalid-operand and wrong-path execute events; not an all-input bound or equivalence proof.'
    return stats


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('runs', type=Path)
    args = p.parse_args()
    rows = [analyze(f.parent) for f in sorted(args.runs.glob('*/result.json'))]
    if not rows:
        raise RuntimeError('No result files')
    (args.runs/'trace_summary.json').write_text(json.dumps(rows,indent=2)+'\n')
    for r in rows:
        print(r['name'], r.get('max_occupancy'), 'region violations',r.get('region_contract_violation_count'))


if __name__ == '__main__':
    main()
