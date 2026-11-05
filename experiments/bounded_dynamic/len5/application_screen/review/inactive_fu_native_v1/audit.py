#!/usr/bin/env python3
"""Read-only audit of native arithmetic plus closed inactive-state facts."""
import copy
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PREVIOUS = HERE.parent / 'inactive_fu_import_v1'
spec = importlib.util.spec_from_file_location('independent_import_audit', PREVIOUS / 'audit.py')
prior = importlib.util.module_from_spec(spec)
spec.loader.exec_module(prior)
read, sha, require = prior.read, prior.sha, prior.require
NATIVE = prior.BUILD / 'harvard_rom_inactive_fu_native_prepare_v1'
ABSTRACT = prior.BUILD / 'harvard_rom_inactive_fu_alu_mul_prepare_v1'


def main():
    info, earlier = read(NATIVE / 'summary.json'), read(ABSTRACT / 'summary.json')
    require(info['status'] == 'prepared_query_only' and info['accepted_optimization'] is False, 'Wrong result scope')
    require(info['abstraction_mode'] == 'none' and info['datapath_abstraction'] is None and
            info['abstraction_helper_sha256'] is None, 'Native arithmetic query contains payload abstraction')
    require(Path(info['query_core_path']) == NATIVE / 'inactive_query_core.json' and
            sha(NATIVE / 'inactive_query_core.json') == info['query_core_sha256'], 'Wrong final query')
    dependencies = {}
    maps = {}
    for name in ('native_word_domain_import', 'external_rom_domain_import', 'inactive_fu_import'):
        current, previous = info[name]['proof_dependencies_sha256'], earlier[name]['proof_dependencies_sha256']
        require({p.replace(str(NATIVE), 'PREP'): value for p, value in current.items()} ==
                {p.replace(str(ABSTRACT), 'PREP'): value for p, value in previous.items()}, 'Theorem dependency set changed')
        for path, value in current.items():
            require(dependencies.get(path, value) == value, 'Conflicting theorem binding')
            dependencies[path] = value
        maps[name] = len(current)
    prior.verify(dependencies)
    identical = ['source.json', 'core.json', 'core.v', 'AdmissionScreen.sv', 'lemma_core.json',
                 'inactive_query_core.json', 'formal_screen.py', 'program_rom.py', 'program.hex', 'temporal.py']
    for name in identical:
        require(sha(NATIVE / name) == sha(ABSTRACT / name), 'Changed baseline artifact: ' + name)
        dependencies[str(ABSTRACT / name)] = sha(ABSTRACT / name)
    prior_summary = read(PREVIOUS / 'summary.json')
    require(prior_summary['status'] == 'independent_inactive_fu_import_integration_review_passed', 'Prior review absent')
    require(sha(ABSTRACT / 'summary.json') == prior_summary['prepared_query_summary_sha256'], 'Prior preparation changed')
    native, lemma, actual = (read(NATIVE / name) for name in ('core.json', 'lemma_core.json', 'inactive_query_core.json'))
    substitutions = {int(bit): value for bit, value in info['inactive_fu_import']['reset_substitutions'].items()}
    expected, deleted, sliced = prior.graph_rewrite(native, substitutions)
    words = info['native_word_domain_import']
    for name in words['added_cells']:
        expected['modules']['datapath']['cells'][name] = copy.deepcopy(lemma['modules']['datapath']['cells'][name])
    require(expected == actual, 'Native query differs beyond proved reset facts and existing word predicates')
    require(len(substitutions) == 1761 and len(deleted) == 80 and len(sliced) == 1, 'Changed reset-fact set')
    module = actual['modules']['datapath']
    require(not any(c['type'] in ('$anyseq', '$anyconst') for c in module['cells'].values()), 'Native graph has symbolic payload driver')
    protected = set(words['source_projection_data_cells']) | set(words['source_projection_preserved_control_cells'])
    require(len(protected) == 57 and len(words['added_cells']) == 119, 'Changed word theorem')
    require(all(module['cells'][name] == native['modules']['datapath']['cells'][name] for name in protected), 'Word projection changed')
    for cut in earlier['datapath_abstraction']['cuts']:
        require(module['cells'][cut['original_cell_name']] == cut['original_cell'], 'Original payload driver not restored')
        require(cut['replacement_cell_name'] not in module['cells'], 'Abstract payload replacement remains')
    model = read(NATIVE / 'screen.json')['modules']['AdmissionScreen']
    counts = {kind: sum(c['type'] == '$' + kind for c in model['cells'].values()) for kind in ('assert', 'assume', 'cover')}
    require(counts == info['query_property_counts'] == {'assert': 3, 'assume': 8, 'cover': 0}, 'Changed obligations')
    require(not any(bit in ('x', 'z') for c in model['cells'].values() for bs in c['connections'].values() for bit in bs), 'Literal undefined proof value')
    require(not any('init' in n.get('attributes', {}) for n in model['netnames'].values()), 'Extra initial state restriction')
    script = (NATIVE / 'prepare.ys').read_text()
    require(script.index('setundef -anyseq') < script.index('prep -top'), 'Undefined values symbolized too late')
    require(script.replace(str(NATIVE), 'PREP').replace('inactive_query_core.json', 'QUERY.json') ==
            (ABSTRACT / 'prepare.ys').read_text().replace(str(ABSTRACT), 'PREP').replace('abstract_query_core.json', 'QUERY.json'), 'Changed lowering pipeline')
    require(info['clock_model'] == earlier['clock_model'], 'Changed clock semantics')
    for name in ('prepare', 'export'):
        execution = info[name]
        require(execution['returncode'] == 0 and not execution['timeout'] and sha(execution['log']) == execution['log_sha256'], 'Failed or changed preparation')
    require(sha(NATIVE / 'screen.aig') == info['aig_sha256'], 'AIG changed')
    with (NATIVE / 'screen.aig').open('rb') as stream:
        header = stream.readline().decode().split()
    require(header == info['aig_header'] and header[4] == '0' and header[6:8] == ['3', '8'], 'AIG property set changed')
    for directory in (NATIVE, PREVIOUS):
        for path in directory.rglob('*'):
            if path.is_file() and '__pycache__' not in path.parts:
                dependencies[str(path)] = sha(path)
    dependencies[str(Path(__file__))] = sha(Path(__file__))
    prior.verify(dependencies)
    result = {'status': 'independent_native_arithmetic_preparation_review_passed', 'new_solver_queries': 0,
              'accepted_optimization': False, 'byte_identical_prior_artifacts': identical,
              'normalized_theorem_dependency_maps_identical': maps, 'exact_whole_query_graph_reconstruction': True,
              'proved_reset_bits_substituted': 1761, 'removed_native_ff_cells': 80, 'sliced_native_ff_cells': sliced,
              'unchanged_word_projection_cells': 57, 'unchanged_word_predicate_cells': 119,
              'native_payload_drivers_restored': [c['original_cell_name'] for c in earlier['datapath_abstraction']['cuts']],
              'payload_symbolic_replacements': 0, 'native_literal_undef_handling': 'Original synthesis-undefined choices retained symbolically before proof optimization; these ordinary choices are distinct from artificial payload overapproximation.',
              'query_properties': counts, 'initialization_attributes': 0, 'remaining_literal_x_z': 0,
              'native_core_sha256': info['core_json_sha256'], 'harness_sha256': info['harness_sha256'],
              'prepared_summary_sha256': sha(NATIVE / 'summary.json'), 'query_core_sha256': info['query_core_sha256'],
              'screen_json_sha256': sha(NATIVE / 'screen.json'), 'aig_sha256': info['aig_sha256'], 'aig_header': header,
              'source_sha256': dependencies, 'all_dependencies_unchanged_before_after': True,
              'new_environmental_or_internal_premises': [],
              'verdict': 'No blocker. This is exactly the previously reviewed reset-fact and seven-word-lemma query before its optional ALU/MUL payload cuts. Original arithmetic is retained under the same source-bound ROM/reset/service contract; the native hardware export remains unchanged.',
              'limits': ['Preparation and theorem composition only; no admission theorem, hardware acceptance, or measured area claim.',
                         'Data service remains the declared arbitrary nonfaulting load model, not a fully fixed application data image.',
                         'No solver target was run in this review.']}
    (HERE / 'summary.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: result[key] for key in ('status', 'exact_whole_query_graph_reconstruction', 'payload_symbolic_replacements', 'query_properties')}))


if __name__ == '__main__':
    main()
