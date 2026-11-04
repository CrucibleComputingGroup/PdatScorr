#!/usr/bin/env python3
"""Check an actual certified hardware pair under a relaxed read-service contract.

A negative result requires an explicit PDR counterexample to a functional
observation. Initial-state pairing remains; the optional state-equality helper
assertion is disabled so a helper-only mismatch cannot count as a negative.
"""
import argparse
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT))
from odc.temporal import digest, prove_pair


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('analysis', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--baseline', type=Path, default=HERE/'results/baseline_v5/baseline.json')
    parser.add_argument('--toolbin', type=Path, required=True)
    parser.add_argument('--abc', default='/usr/local/bin/abc')
    parser.add_argument('--spacing', type=int, default=3)
    parser.add_argument('--latency', type=int, default=5)
    parser.add_argument('--unordered', action='store_true')
    parser.add_argument('--timeout', type=float, default=120)
    args = parser.parse_args()
    analysis, out = args.analysis.resolve(), args.output.resolve()
    if out.exists():
        raise SystemExit('Refusing existing negative-control output')
    positive = json.loads((analysis/'report.json').read_text())
    assert positive['status'] == 'proved' and positive['combined_proof']['proven']
    assert digest(args.baseline) == positive['design_sha256']
    reference, candidate = analysis/'reference.v', analysis/'optimized.v'
    assert digest(reference) == positive['combined_proof']['reference_sha256']
    assert digest(candidate) == positive['combined_proof']['candidate_sha256']
    out.mkdir(parents=True)
    harness = out/'harness.sv'
    command = [sys.executable, str(HERE/'make_miter.py'), str(args.baseline.resolve()),
               str(harness), '--spacing', str(args.spacing), '--latency', str(args.latency)]
    if args.unordered:
        command.append('--unordered')
    subprocess.run(command, check=True, timeout=10)
    shutil.copy2(ROOT/'odc/temporal.py', out/'temporal_source.py')
    proof = prove_pair(reference, candidate, harness, 'TemporalMiter', out/'proof',
        yosys=str(args.toolbin.resolve()/'yosys'),
        smtbmc=str(args.toolbin.resolve()/'yosys-smtbmc'), solver='z3', depth=12,
        timeout=args.timeout, engine='pdr', abc=args.abc,
        assert_state_correspondence=False)
    assert digest(out/'temporal_source.py') == proof['implementation_sha256']
    model = json.loads((out/'proof/miter.json').read_text())['modules']['TemporalMiter']
    assert '$pscorr_initial_state_assume' in model['cells']
    assert '$pscorr_initial_state_invariant' not in model['cells']
    assert proof['initial_state']['paired_state_bits'] == 343
    assert proof['property_counts']['assert'] == 14
    assert sum(c['type'] == '$assert' for c in model['cells'].values()) == 14
    pdr = proof.get('pdr', {})
    log = Path(pdr['log']).read_text() if 'log' in pdr else ''
    matches = re.findall(r'(?m)^Output\s+\d+[^\n]*\bwas asserted\b[^\n]*', log)
    is_negative = (pdr.get('returncode') == 0 and not pdr.get('timeout', True)
                   and len(matches) == 1 and not proof['proven'])
    result = {
        'status': 'functional_counterexample' if is_negative else 'unresolved',
        'contract': {'min_spacing': args.spacing, 'max_latency': args.latency,
                     'ordered': not args.unordered},
        'scope': 'Actual automatically rewritten hardware versus original native component; all545 defined output bits; no state-helper assertion',
        'reference_sha256': digest(reference), 'candidate_sha256': digest(candidate),
        'baseline_json_sha256': digest(args.baseline),
        'positive_report_sha256': digest(analysis/'report.json'),
        'harness_sha256': digest(harness),
        'monitor_sha256': digest(HERE/'ReadServiceContract.sv'),
        'generator_sha256': digest(HERE/'make_miter.py'),
        'generator_command': command,
        'implementation_sha256': proof['implementation_sha256'],
        'proof_sha256': digest(out/'proof/proof.json'),
        'functional_assertions': 14, 'paired_initial_state_bits': 343,
        'assert_state_correspondence': False, 'counterexample_result': matches,
    }
    (out/'summary.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
    return 0 if is_negative else 1


if __name__ == '__main__':
    raise SystemExit(main())
