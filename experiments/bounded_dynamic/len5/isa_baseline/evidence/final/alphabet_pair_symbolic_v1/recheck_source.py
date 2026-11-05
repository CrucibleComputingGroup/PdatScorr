#!/usr/bin/env python3
"""Reprove a frozen component pair after a proof-backend correction."""
import argparse
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[3]))
sys.path.insert(0, str(HERE.parent))
from odc.temporal import digest, prove_pair
import odc.temporal as temporal_backend
from prepare_frontend import workspace_root


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--candidate', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--yosys', default=str(workspace_root(HERE)/'tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys'))
    parser.add_argument('--timeout', type=int, default=120)
    args = parser.parse_args()
    source, out = args.candidate.resolve(), args.output.resolve(); out.mkdir(parents=True, exist_ok=False)
    old = json.loads((source/'summary.json').read_text())
    previous = old['combined_all_output_proof']
    for key, name in [('reference', 'reference.v'), ('candidate', 'candidate.v'), ('harness', 'harness.sv')]:
        assert digest(source/name) == previous[key+'_sha256']
    helper = old.get('component_kind') == 'architectural_register_file'
    (out/'temporal_source.py').write_bytes(Path(temporal_backend.__file__).read_bytes())
    (out/'recheck_source.py').write_bytes(Path(__file__).read_bytes())
    result = prove_pair(source/'reference.v', source/'candidate.v', source/'harness.sv', 'TemporalMiter', out/'proof',
        yosys=args.yosys, smtbmc=str(Path(args.yosys).with_name('yosys-smtbmc')), solver='z3', depth=3,
        timeout=args.timeout, engine='pdr', abc='/usr/local/bin/abc', assert_state_correspondence=helper)
    safe_undefined = result.get('undefined_value_model', '').startswith('Independent symbolic choices before process optimization')
    assert result['implementation_sha256'] == digest(out/'temporal_source.py')
    record = {'status': 'proved' if result['proven'] and safe_undefined else 'unproved', 'proof': result,
              'candidate_summary_sha256': digest(source/'summary.json'),
              'native_candidate_sha256': digest(source/'candidate_whole_core.json'),
              'candidate_directory': str(source), 'script_sha256': digest(Path(__file__)),
              'component_kind': old.get('component_kind', 'instruction_decoder'),
              'independent_undefined_choices': safe_undefined, 'assumptions_or_observations_changed': False}
    (out/'summary.json').write_text(json.dumps(record, indent=2)+'\n')
    print(json.dumps({'status': record['status'], 'component': record['component_kind'], 'directory': str(out)}))
    return 0 if record['status'] == 'proved' else 1


if __name__ == '__main__':
    raise SystemExit(main())
