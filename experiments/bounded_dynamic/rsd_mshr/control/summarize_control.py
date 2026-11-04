#!/usr/bin/env python3
"""Audit and combine two matched correspondence controls; never claim cell area."""
import argparse
import hashlib
import json
from pathlib import Path


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--original', type=Path, required=True)
    parser.add_argument('--optimized', type=Path, required=True)
    parser.add_argument('--proof-report', type=Path,
                        help='Optional completed automatic-discovery report to bind to these exact JSON inputs')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    sources = [(label, folder.resolve(), json.loads((folder/'summary.json').read_text()))
               for label, folder in [('original', args.original), ('automatic_equality_cut', args.optimized)]]
    first = sources[0][2]
    matched_fields = ['contract', 'monitor_sha256', 'functional_input_bits',
                      'functional_output_bits', 'native_ff_bits', 'wrapper_sha256']
    rows, artifacts = [], {}
    for label, folder, report in sources:
        assert report['status'] == 'complete_formal_control'
        assert all(report[field] == first[field] for field in matched_fields)
        assert report['provenance']['tools'] == first['provenance']['tools']
        assert report['provenance']['script_sha256'] == first['provenance']['script_sha256']
        assert not report['physical_mapping_permitted']
        assert sha(Path(report['baseline'])) == report['baseline_sha256']
        artifacts[str(folder/'summary.json')] = sha(folder/'summary.json')
        for relative in ('prepare.ys', 'prepare.log', 'PscorrControl.sv', 'ReadServiceContract.sv',
                         'runner_snapshot.py', 'temporal_snapshot.py'):
            artifacts[str(folder/relative)] = sha(folder/relative)
        assert sha(folder/'runner_snapshot.py') == report['provenance']['script_sha256']
        assert sha(folder/'temporal_snapshot.py') == report['provenance']['temporal_sha256']
        for mode in ('no_scorr', 'scorr'):
            variant = report['variants'][mode]
            assert variant['depth'] == first['variants'][mode]['depth']
            assert variant['status'] == 'complete' and variant['outputs_preserved']
            assert not variant['command_result']['timeout'] and variant['command_result']['returncode'] == 0
            assert sha(folder/mode/'logic.aig') == variant['aig_sha256']
            assert sha(folder/mode/'abc.log') == variant['command_result']['log_sha256']
            for relative in ('abc.log', 'run.abc', 'logic.aig'):
                artifacts[str(folder/mode/relative)] = sha(folder/mode/relative)
            final = variant['final']
            rows.append({'hardware_input': label, 'correspondence': mode,
                         'formal_ands': final['ands'], 'formal_latches': final['latches'],
                         'formal_inputs': final['inputs'], 'functional_outputs': final['outputs'],
                         'source_json_sha256': report['baseline_sha256']})
    original = json.loads(Path(first['baseline']).read_text())['modules']['MshrObserved']
    optimized = json.loads(Path(sources[1][2]['baseline']).read_text())['modules']['MshrObserved']
    assert original['ports'] == optimized['ports']
    assert original['cells'].keys() == optimized['cells'].keys()
    changed = []
    for name, cell in original['cells'].items():
        after = optimized['cells'][name]
        if cell != after:
            assert cell['type'] == after['type'] == '$eq'
            changed.append({'cell': name, 'original_width': int(cell['parameters']['A_WIDTH'],2),
                            'optimized_width': int(after['parameters']['A_WIDTH'],2)})
    result = {'scope': 'Formal encoding counts only; not physical area and not a standalone equivalence certificate',
              'contract': first['contract'], 'monitor_sha256': first['monitor_sha256'],
              'native_ff_bits': first['native_ff_bits'],
              'changed_hardware_cells': changed, 'rows': rows,
              'limitations': ['Formal monitor and initialization encoding may remain in these AIGs.',
                              'Nondeterministic undefined values and initial-state inputs are not hardware input ports.',
                              'Automatic candidate proof must be checked separately; these controls never authorize an RTL rewrite.'],
              'artifact_sha256': artifacts}
    if args.proof_report is not None:
        proof_path = args.proof_report.resolve()
        proof = json.loads(proof_path.read_text())
        assert proof['status'] == 'proved' and proof['combined_proof']['proven']
        assert proof['design_sha256'] == first['baseline_sha256']
        assert proof['optimized_json_sha256'] == sources[1][2]['baseline_sha256']
        combined = proof['combined_proof']
        assert combined['candidate_sha256'] == proof['optimized_verilog_sha256']
        assert combined['pdr']['returncode'] == 0 and not combined['pdr']['timeout']
        assert sha(Path(combined['pdr']['log'])) == combined['pdr']['log_sha256']
        assert sha(proof_path.parent/'optimized.v') == proof['optimized_verilog_sha256']
        assert sha(proof_path.parent/'harness.sv') == proof['harness_sha256']
        result['automatic_proof_binding'] = {
            'report': str(proof_path), 'report_sha256': sha(proof_path),
            'method': combined['method'], 'accepted_equality_count': len(proof['accepted']),
            'combined_proof': combined, 'harness_sha256': proof['harness_sha256']}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(rows,indent=2))


if __name__ == '__main__':
    main()
