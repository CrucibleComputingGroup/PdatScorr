#!/usr/bin/env python3
"""Compact a frozen reset-cube certificate after exact source/patch checks."""
import argparse
import collections
import json
from pathlib import Path

import reset_cube
import reset_cube_fixedpoint as fixed
from reset_cube import digest, eligibility, project, read, require


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--run', type=Path, required=True)
    p.add_argument('--evidence', type=Path, required=True)
    args = p.parse_args()
    run, evidence = args.run.resolve(), args.evidence.resolve()
    record = read(run/'summary.json')
    require(record['status'] == 'reset_cube_certified_query_patch_only' and record['accepted_optimization'] is False,
            'No certified query-only cube')
    for path, value in record['dependencies_sha256'].items():
        require(digest(Path(path)) == value, 'Proof source changed')
    require(digest(run/'source.json') == record['source_sha256'], 'Source snapshot changed')
    require(digest(run/'query_only_patch.json') == record['query_only_patch_sha256'], 'Patch graph changed')
    source, patched = read(run/'source.json'), read(run/'query_only_patch.json')
    rows = read(run/'selected_words.json')
    eligible, _ = eligibility(source, 'datapath')
    known = {row['name']: row for row in eligible}
    require(len({row['name'] for row in rows}) == len(rows), 'Duplicate selected word')
    require(all(known[row['name']] == row for row in rows), 'Selected word does not match native FF primitive')
    expected, patch = fixed.patch_constants(source, 'datapath', rows)
    require(expected == patched, 'Exact query patch differs')
    graph = fixed.audit_patch(source, patched, 'datapath', patch)
    require(graph == record['graph_audit'], 'Recorded graph audit differs')
    proofs = {}
    for mode in ('induction', 'base'):
        directory = run/f'final_{mode}'
        proof = record['final_proofs'][mode]
        require(proof['status'] == 'proved_combinationally', 'Missing final SAT proof')
        projection, audit = project(source, 'datapath', rows, mode=mode)
        require(projection == read(directory/'projection.json') and json.loads(json.dumps(audit)) == read(directory/'projection_audit.json'),
                'Final proof differs from exact source-derived primitive cone')
        require(digest(directory/'projection.json') == proof['projection_sha256'] and
                digest(directory/'lowered.json') == proof['lowered_sha256'], 'Final proof model changed')
        require(digest(directory/'sat.log') == proof['sat_log_sha256'], 'Final SAT log changed')
        log = (directory/'sat.log').read_text()
        require(log.count('SAT proof finished - no model found: SUCCESS!') == 1 and
                'SAT proof finished - model found: FAIL!' not in log, 'SAT proof outcome differs')
        script = (directory/'sat_execution/run.ys').read_text()
        reset_arg = ' -set rst_ni 0' if mode == 'base' else ''
        expected_script = f'read_json {reset_cube.quoted(directory/"lowered.json")}\ncheck -assert\n'
        expected_script += f'tee -o {reset_cube.quoted(directory/"sat.log")} sat -set-def-inputs{reset_arg} -prove cube_bad 0 -show-ports -dump_json {reset_cube.quoted(directory/"counterexample.json")}\n'
        require(script == expected_script, 'Final SAT command has altered premise or target')
        for execution in (proof['symbolize_execution'], proof['execution'], proof['sat_execution']):
            path = Path(execution['argv'][-1])
            require(execution['returncode'] == 0 and not execution['timeout'] and
                    digest(path) == execution['script_sha256'] and digest(path.parent/'run.log') == execution['log_sha256'],
                    'Final proof execution changed or failed')
        lowered = read(directory/'lowered.json')['modules']['ResetCube']
        require(not any(reset_cube.state_cell(c) or c['type'] in reset_cube.FORBIDDEN | {'$anyseq', '$anyconst'}
                        for c in lowered['cells'].values()), 'Hidden state, choice primitive, or premise in final SAT model')
        require(not any(bit in ('x', 'z') for c in lowered['cells'].values() for bits in c['connections'].values() for bit in bits),
                'Undefined literal in final SAT model')
        proofs[mode] = {'status': proof['status'], 'source_projection_sha256': proof['projection_sha256'],
                       'lowered_sha256': proof['lowered_sha256'], 'sat_log_sha256': proof['sat_log_sha256'],
                       'sat_execution': proof['sat_execution'], 'lowered_cells': proof['lowered_cells'],
                       'reset_premise': audit['reset_base_premise'], 'source_projection_reconstructed_exactly': True}
    groups = collections.defaultdict(lambda: {'words': 0, 'bits': 0})
    for row in rows:
        name = row['name']
        group = 'DIV pipeline/operands/arbiters' if 'gen_div_unit' in name else 'MUL pipeline/operands/arbiters' if 'gen_mult_unit' in name else 'store-buffer speculative flags'
        groups[group]['words'] += 1
        groups[group]['bits'] += row['width']
    tiny = read(run.parent/'reset_cube_all_tiny_v1_execution.json')
    require(tiny['returncode'] == 0 and digest(run.parent/'reset_cube_all_tiny_v1.log') == tiny['log_sha256'], 'Persistent tests failed or changed')
    initial = run.parent/'reset_cube_native_prepare_v1/summary.json'
    initial_record = read(initial)
    result = {'status': record['status'], 'accepted_hardware_optimization': False, 'query_only': True,
              'source_run': str(run), 'source_summary_sha256': digest(run/'summary.json'),
              'original_property_free_input_sha256': record['source_sha256'],
              'runner_sources_sha256': {str(path): digest(path) for path in
                  (Path(reset_cube.__file__), Path(fixed.__file__), Path(__file__))},
              'initial_prepare_only_summary': {'path': str(initial), 'sha256': digest(initial),
                  'eligible_words': initial_record['eligibility']['eligible_words'],
                  'eligible_bits': initial_record['eligibility']['eligible_bits'],
                  'cofactor': initial_record['initial_cofactor_summary'], 'native_sat_queries': 0},
              'rounds': [{'index': r['index'], 'candidate_words': r['candidate_words'], 'candidate_bits': r['candidate_bits'],
                         'kept_words': r['kept_words'], 'discarded_words': len(r['discarded_words']),
                         'prepared_cells': r['cofactor']['lowered_cells']} for r in record['rounds']],
              'certified_words': record['certified_words'], 'certified_bits': record['certified_bits'],
              'groups': dict(groups), 'final_proofs': proofs, 'graph_audit': graph,
              'query_only_patch_sha256': record['query_only_patch_sha256'],
              'selected_words_sha256': digest(run/'selected_words.json'), 'patch_sha256': digest(run/'patch.json'),
              'elapsed_seconds': record['elapsed_seconds'], 'final_proof_seconds': record['final_proof_seconds'],
              'source_dependency_count': len(record['dependencies_sha256']), 'source_dependencies_verified': True,
              'validation': {'tests_passed': 16, 'execution': tiny, 'includes_false_fixedpoint_negative': True},
              'new_admission_or_timing_premises': [], 'main_query_integrated': False, 'physical_map_performed': False,
              'interpretation': 'A source-bound, reset-conditioned constant cube for a separately proved property-free input graph. Native arithmetic is retained. The two final combinational SAT checks establish reset base and simultaneous transition closure. This is additional proof-model simplification, not an ALU admission theorem, timing savings, or accepted hardware optimization.'}
    for path, value in record['dependencies_sha256'].items():
        require(digest(Path(path)) == value, 'Proof dependency changed during reporting')
    target = evidence/'result_summary.json'
    require(not target.exists(), 'Do not overwrite a frozen report')
    target.write_text(json.dumps(result, indent=2)+'\n')
    (evidence/'sources/reset_cube_report.py').write_bytes(Path(__file__).read_bytes())
    manifest = read(evidence/'manifest.json')
    manifest['derived_reports'] = {'result_summary.json': digest(target),
                                   'sources/reset_cube_report.py': digest(evidence/'sources/reset_cube_report.py')}
    (evidence/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
    (evidence/'SHA256SUMS').write_text(''.join(f'{digest(path)}  {path.relative_to(evidence)}\n'
        for path in sorted(evidence.rglob('*')) if path.is_file() and path.name != 'SHA256SUMS'))
    print(json.dumps({'status': result['status'], 'words': result['certified_words'], 'bits': result['certified_bits'],
                      'summary_sha256': digest(target), 'manifest_sha256': digest(evidence/'SHA256SUMS')}))


if __name__ == '__main__':
    main()
