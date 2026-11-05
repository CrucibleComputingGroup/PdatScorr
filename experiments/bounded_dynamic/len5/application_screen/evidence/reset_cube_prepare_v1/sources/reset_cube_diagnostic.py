#!/usr/bin/env python3
"""Prepare one native reset-cube cofactor; never certify or solve its cube."""
import argparse
import collections
import json
from pathlib import Path

from reset_cube import digest, discover, read, require
import reset_cube

HERE = Path(__file__).resolve().parent
BUILD = Path('/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--yosys', type=Path, required=True)
    args = p.parse_args()
    original = BUILD/'inactive_fu_lemmas_v1/query_only.json'
    prior_path = HERE/'review/inactive_fu_lemmas_v1/summary.json'
    prior = read(prior_path)
    require(prior['status'] == 'independent_end_to_end_composition_review_passed', 'Missing closed native input review')
    require(digest(original) == prior['query_sha256'] == 'bb52d686f974809e0bebd4e2b373414ec9a53af34cff5a6a48d1e5ab2465307b', 'Wrong property-free source')
    dependencies = dict(prior['source_sha256'])
    for path in (original, prior_path, Path(__file__), Path(reset_cube.__file__)):
        dependencies[str(path)] = digest(path)
    for path, value in dependencies.items():
        require(digest(Path(path)) == value, 'Input theorem dependency changed: ' + path)
    design = read(original)
    require(not any(c['type'] in ('$assert', '$assume', '$cover', '$check', '$anyseq', '$anyconst')
                    for c in design['modules']['datapath']['cells'].values()), 'Expected property-free certified reset-fact graph')
    result = discover(design, 'datapath', args.output, yosys=args.yosys, timeout=30, prepare_only=True)
    require(result['status'] == 'prepared_only_no_invariant_certificate', 'Native cofactor preparation failed')
    proof = result['rounds'][0]['proof']
    values = proof['initial_cofactor_output_constants'].values()
    counts = {'constant_zero': sum(x == '0' for x in values), 'constant_one': sum(x == '1' for x in values),
              'dynamic': sum(type(x) is int for x in values)}
    result.update(original_input_path=str(original), original_input_sha256=digest(original),
        input_scope='Previously source-closed 1761-bit inactive-FU query-only reset substitution, before word-lemma cells or payload cuts; not the unchanged hardware export.',
        input_theorem_dependencies_sha256=dependencies, initial_cofactor_summary=counts,
        native_sat_queries=0, native_invariants_accepted=0, native_fixed_point_computed=False,
        interpretation='An initial all-candidate cofactor and preparation-size diagnostic only. A zero bad output under this provisional cube does not establish an invariant after other candidates are discarded. No native cube or simplification is accepted.')
    for path, value in dependencies.items():
        require(digest(Path(path)) == value, 'Input theorem dependency changed during diagnostic: ' + path)
    (args.output/'summary.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'status': result['status'], 'eligible_words': result['eligibility']['eligible_words'],
        'eligible_bits': result['eligibility']['eligible_bits'], 'cofactor': counts,
        'prepared_cells': proof['lowered_cells'], 'native_sat_queries': 0, 'native_invariants_accepted': 0}))


if __name__ == '__main__':
    main()
