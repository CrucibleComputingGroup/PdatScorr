#!/usr/bin/env python3
"""Retain and validate an ABC witness for an already-disproved component miter."""
import argparse
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[2]))
from odc.temporal import digest, run_command


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('negative', type=Path)
    parser.add_argument('--timeout', type=float, default=120)
    args = parser.parse_args()
    run = args.negative.resolve()
    summary = json.loads((run/'summary.json').read_text())
    assert summary['status'] == 'functional_counterexample'
    proof = json.loads((run/'proof/proof.json').read_text())
    assert digest(run/'proof/proof.json') == summary['proof_sha256']
    assert digest(run/'proof/miter.aig') == proof['aig_sha256']
    out = run/'witness'
    out.mkdir(exist_ok=False)
    for p in [out/'counterexample.txt', out/'counterexample.aiw', out/'folded.aig']:
        if any(c in str(p) for c in [';', '"', '\\', '\n', '\r']):
            raise ValueError('Unsupported ABC path')
    # Use exactly the archived proof's AIG reader, constraint folding, property
    # OR, and PDR command. Only witness export/validation commands are appended.
    command = proof['pdr']['argv'][2]
    command += '; testcex -a'
    command += f'; write_cex -n -c "{out / "counterexample.txt"}"'
    command += f'; write_cex -a "{out / "counterexample.aiw"}"'
    command += f'; write_aiger "{out / "folded.aig"}"'
    (out/'run.abc').write_text(command+'\n')
    execution = run_command([proof['pdr']['argv'][0], '-c', command],
                            out/'abc.log', args.timeout+5)
    log = (out/'abc.log').read_text()
    counterexamples = re.findall(r'(?m)^Output\s+\d+[^\n]*\bwas asserted\b[^\n]*', log)
    assert execution['returncode'] == 0 and not execution['timeout']
    assert len(counterexamples) == 1
    assert 'Main AIG: The cex is correct.' in log
    assert not re.search(r'(?im)^.*\b(error|incorrect|verification failed)\b', log)
    for name in ['counterexample.txt', 'counterexample.aiw', 'folded.aig']:
        assert (out/name).stat().st_size > 0
    record = {'status': 'validated_functional_counterexample',
        'scope': 'Same archived functional-only miter and PDR command; ABC testcex -a validates before write_cex',
        'input_aig_sha256': proof['aig_sha256'],
        'negative_summary_sha256': digest(run/'summary.json'),
        'abc_sha256': digest(Path(proof['pdr']['argv'][0])),
        'execution': execution, 'counterexample_result': counterexamples,
        'artifact_sha256': {name:digest(out/name) for name in
                           ['counterexample.txt', 'counterexample.aiw', 'folded.aig', 'run.abc']}}
    (out/'summary.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record,indent=2))


if __name__ == '__main__':
    main()
