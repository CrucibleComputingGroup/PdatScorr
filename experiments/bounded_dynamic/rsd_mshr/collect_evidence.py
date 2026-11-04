#!/usr/bin/env python3
"""Audit completed component proofs and extract compact, source-bound witnesses.

Reads existing results only. It does not run a synthesis or formal solver.
"""
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def trace_rows(path):
    """Read the small SMTBMC VCD subset, discarding its final clock-only tick."""
    scope, names, rows, values, updated = [], {}, [], {}, set()
    in_header = True
    timestamp = None
    wanted = {'rst', 'allocated_id', 'read_accept', 'response_valid',
              'response_id', 'saved0', 'saved1', 'waiting0', 'waiting1',
              'service.count', 'service.queue_id<0>', 'service.queue_id<1>',
              'service.queue_id<2>', 'service.queue_id<3>'}

    def flush():
        # All data fields are dumped at the actual SMT state; the synthetic
        # trailing VCD tick only changes clocks and smt_step.
        if timestamp is not None and 'rst' in updated:
            row = {'cycle': values['smt_step']}
            row.update({k: values[k] for k in sorted(wanted) if k in values})
            rows.append(row)

    for line in path.read_text().splitlines():
        fields = line.split()
        if in_header:
            if line.startswith('$scope'):
                scope.append(fields[2])
            elif line.startswith('$upscope'):
                scope.pop()
            elif line.startswith('$var'):
                full = '.'.join(scope[1:] + [fields[4]])
                if full in wanted or full == 'smt_step':
                    names[fields[3]] = full
            elif line.startswith('$enddefinitions'):
                in_header = False
        elif line.startswith('#'):
            flush()
            timestamp = int(line[1:])
            updated = set()
        elif line.startswith('b') and len(fields) == 2:
            if fields[1] in names:
                name = names[fields[1]]
                assert set(fields[0][1:]) <= {'0', '1'}, (path, name, line)
                values[name] = int(fields[0][1:], 2)
                updated.add(name)
    flush()
    assert rows, path
    return rows


def failures(row):
    if row['rst'] or not row['response_valid']:
        return []
    return [i for i in range(2) if row[f'waiting{i}'] and
            (row[f'saved{i}'] & 1) == (row['response_id'] & 1) and
            (row[f'saved{i}'] >> 1) != (row['response_id'] >> 1)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    if args.output.exists():
        raise SystemExit('Refusing existing evidence output')
    base = HERE/'results/baseline_v5'
    proof = HERE/'results/proof_v6'
    manifest = json.loads((base/'manifest.json').read_text())
    assert manifest['status'] == 'complete'
    for name, digest in manifest['source_sha256'].items():
        assert sha(base/'src'/name) == digest, name
    assert sha(base/'MshrObserved.sv') == manifest['wrapper_sha256']
    assert sha(HERE/'MshrObserved.sv') == manifest['wrapper_sha256']
    design = json.loads((base/'baseline.json').read_text())['modules']['MshrObserved']
    binding = json.loads((proof/'invariant_bindings.json').read_text())
    assert sha(base/'baseline.json') == binding['baseline_json_sha256']
    assert sha(proof/'summary.json') == binding['proof_summary_sha256']
    assert sha(proof/'model.smt2') == binding['proof_model_sha256']
    assert sha(proof/'MshrTimingProof.sv') == binding['harness_sha256']
    assert sha(HERE/'ReadServiceContract.sv') == binding['service_contract_sha256']
    for item in binding['bindings'].values():
        bits = design['netnames'][item['baseline_net']]['bits']
        assert [bits[i] for i in item['positions_lsb_first']] == item['baseline_bits']
    proof_design = json.loads((proof/'proof_flat.json').read_text())['modules']['MshrTimingProof']
    assert sum(c['type'] == '$assert' for c in proof_design['cells'].values()) == 18
    assert sum(c['type'] == '$cover' for c in proof_design['cells'].values()) == 4
    assert 'Status: PASSED' in (proof/'base.log').read_text()
    assert 'Temporal induction successful' in (proof/'induction.log').read_text()
    assert 'Status: PASSED' in (proof/'induction.log').read_text()

    covers = []
    cover_dir = proof
    cover_summary = json.loads((proof/'summary.json').read_text())
    assert cover_summary['model_sha256'] == sha(proof/'model.smt2')
    assert cover_summary['status'] == 'passed'
    assert 'Status: PASSED' in (proof/'cover.log').read_text()
    traces = sorted(p.name for p in cover_dir.glob('cover_*.vcd'))
    assert len(traces) == 4
    for name in traces:
        rows = trace_rows(cover_dir/name)
        assert not any(failures(row) for row in rows)
        covers.append({'path': str((cover_dir/name).relative_to(HERE)),
                       'sha256': sha(cover_dir/name), 'rows': rows})
    def hits(predicate):
        return [{'trace': c['path'], 'cycle': r['cycle']}
                for c in covers for r in c['rows'] if not r['rst'] and predicate(r)]
    coverage = {
        'two_waiting_mshrs_and_pending_reads': hits(lambda r: r['service.count'] == 2 and r['waiting0'] and r['waiting1']),
        'owner0_raw_high_match_false': hits(lambda r: r['waiting0'] and r['response_valid'] and (r['saved0'] >> 1) != (r['response_id'] >> 1)),
        'owner1_raw_high_match_false': hits(lambda r: r['waiting1'] and r['response_valid'] and (r['saved1'] >> 1) != (r['response_id'] >> 1)),
    }
    assert all(coverage.values())
    wraps = []
    for c in covers:
        accepted = [r for r in c['rows'] if not r['rst'] and r['read_accept']]
        for a, b in zip(accepted, accepted[1:]):
            if a['allocated_id'] == 3 and b['allocated_id'] == 0:
                wraps.append({'trace': c['path'], 'cycles': [a['cycle'], b['cycle']]})
    assert wraps
    coverage['allocated_id_wrap_3_to_0'] = wraps

    negatives = []
    for dirname in ['negative_deadline_v1', 'negative_order_v1']:
        run = HERE/'results'/dirname
        summary = json.loads((run/'summary.json').read_text())
        assert summary['status'] == 'negative_witness'
        assert summary['service_contract_sha256'] == sha(HERE/'ReadServiceContract.sv')
        assert summary['harness_sha256'] == sha(run/'MshrTimingProof.sv')
        harness = (run/'MshrTimingProof.sv').read_text()
        assert harness.count('assert(') == 2  # Only target properties, no support lemma.
        log = (run/'negative.log').read_text()
        assert 'Status: FAILED' in log and 'Assert failed in MshrTimingProof:' in log
        rows = trace_rows(run/'negative.vcd')
        failing = [{'cycle': r['cycle'], 'owners': failures(r)} for r in rows if failures(r)]
        assert failing
        negatives.append({'path': str(run.relative_to(HERE)), 'contract': summary['contract'],
                          'scope': 'Historical baseline_v3 with extra external read-busy input; not the final native baseline_v5 boundary',
                          'summary_sha256': sha(run/'summary.json'),
                          'trace_sha256': sha(run/'negative.vcd'),
                          'model_sha256': sha(run/'model.smt2'),
                          'failures': failing, 'rows': rows})
    result = {
        'status': 'passed', 'scope': 'Original-component local mechanism proof; not full-core equivalence, workload adherence, or hardware area',
        'rsd_revision': manifest['rsd_revision'],
        'baseline_manifest_sha256': sha(base/'manifest.json'),
        'baseline_json_sha256': sha(base/'baseline.json'),
        'baseline_verilog_sha256': sha(base/'baseline.v'),
        'source_file_count': len(manifest['source_sha256']),
        'port_bits': manifest['port_bits'],
        'flip_flop_bits': sum(len(c['connections']['Q']) for c in design['cells'].values() if c['type'] == '$dff'),
        'equality_cells': sum(c['type'] == '$eq' for c in design['cells'].values()),
        'contract': json.loads((proof/'summary.json').read_text())['contract'],
        'assertion_count': 18, 'coverage': coverage, 'cover_traces': covers,
        'historical_negative_controls': negatives,
        'proof_summary_sha256': sha(proof/'summary.json'),
        'binding_manifest_sha256': sha(proof/'invariant_bindings.json'),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ['cover_traces', 'historical_negative_controls']}, indent=2))


if __name__ == '__main__':
    main()
