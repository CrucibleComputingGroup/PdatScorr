#!/usr/bin/env python3
"""Independent frozen inactive-FU integration audit; no exporter or solver runs."""
import copy
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
APP = HERE.parents[1]
BUILD = Path('/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build')
PREPARED = BUILD / 'harvard_rom_inactive_fu_alu_mul_prepare_v1'
PRIOR = BUILD / 'harvard_rom_word_lemmas_alu_mul_prepare_v1'
RAW = BUILD / 'inactive_fu_lemmas_v1'


def read(path):
    return json.loads(Path(path).read_text())


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def require(value, message):
    if not value:
        raise ValueError(message)


def verify(dependencies):
    for path, expected in dependencies.items():
        require(sha(path) == expected, 'Dependency changed: ' + path)


def graph_rewrite(native, substitutions):
    """Independently slice only native visible async-load reset FF outputs."""
    result = copy.deepcopy(native)
    module = result['modules']['datapath']
    found, deleted, sliced = set(), [], []
    for name, cell in list(module['cells'].items()):
        outputs = {bit for pin, direction in cell['port_directions'].items()
                   if direction == 'output' for bit in cell['connections'][pin]}
        selected = outputs & set(substitutions)
        if not selected:
            continue
        require(cell['type'] == '$aldff' and outputs == set(cell['connections']['Q']), 'Non-native-FF substitution')
        require(cell['connections']['CLK'] == [2] and cell['connections']['ALOAD'] == [3], 'Different reset/clock')
        require(int(cell['parameters']['CLK_POLARITY'], 2) == 1 and
                int(cell['parameters']['ALOAD_POLARITY'], 2) == 0, 'Different reset polarity')
        for index, bit in enumerate(cell['connections']['Q']):
            if bit in selected:
                require(cell['connections']['AD'][index] == substitutions[bit] == '0', 'Wrong reset constant')
        found |= selected
        keep = [i for i, bit in enumerate(cell['connections']['Q']) if bit not in selected]
        if keep:
            for pin in ('AD', 'D', 'Q'):
                cell['connections'][pin] = [cell['connections'][pin][i] for i in keep]
            cell['parameters']['WIDTH'] = format(len(keep), '032b')
            sliced.append(name)
        else:
            del module['cells'][name]
            deleted.append(name)
    require(found == set(substitutions), 'Missing native reset-state driver')
    for cell in module['cells'].values():
        for pin, direction in cell['port_directions'].items():
            if direction == 'input':
                cell['connections'][pin] = [substitutions.get(bit, bit) for bit in cell['connections'][pin]]
    for collection in ('ports', 'netnames'):
        for item in module[collection].values():
            item['bits'] = [substitutions.get(bit, bit) for bit in item['bits']]
    return result, deleted, sliced


def check_graph(native, lemma, reduced, abstract, info):
    words = info['native_word_domain_import']
    facts = info['inactive_fu_import']
    substitutions = {int(bit): value for bit, value in facts['reset_substitutions'].items()}
    require(len(substitutions) == 1761 and substitutions[91687] == '0', 'Unexpected reset-fact set')
    stripped = copy.deepcopy(lemma)
    for name in words['added_cells']:
        del stripped['modules']['datapath']['cells'][name]
    require(stripped == native, 'Word model changed native graph')
    expected, deleted, sliced = graph_rewrite(native, substitutions)
    require(len(deleted) == 80 and len(sliced) == 1, 'Unexpected state-removal inventory')
    for name in words['added_cells']:
        cell = lemma['modules']['datapath']['cells'][name]
        require(not any(set(bits) & set(substitutions) for bits in cell['connections'].values()), 'Reset fact overlaps lemma')
        expected['modules']['datapath']['cells'][name] = copy.deepcopy(cell)
    require(expected == reduced, 'Composed graph differs beyond exact proved constants and old lemmas')
    protected = set(words['source_projection_data_cells']) | set(words['source_projection_preserved_control_cells'])
    require(len(protected) == 57 and len(words['added_cells']) == 119, 'Unexpected word theorem inventory')
    for name in protected:
        require(native['modules']['datapath']['cells'][name] == reduced['modules']['datapath']['cells'][name], 'Word projection changed')
    for cut in info['datapath_abstraction']['cuts']:
        name = cut['original_cell_name']
        cell = expected['modules']['datapath']['cells'].pop(name)
        require(cell == cut['original_cell'], 'Abstraction driver differs')
        require(name not in protected and len(cut['output_bits']) == 64, 'Unexpected abstracted control or word driver')
        replacement = abstract['modules']['datapath']['cells'][cut['replacement_cell_name']]
        require(replacement['type'] == '$anyseq' and replacement['connections'] == {'Y': cut['output_bits']}, 'Wrong payload replacement')
        expected['modules']['datapath']['cells'][cut['replacement_cell_name']] = copy.deepcopy(replacement)
    require(info['abstraction_mode'] == 'alu_mul' and len(info['datapath_abstraction']['cuts']) == 2, 'Unexpected abstraction scope')
    require(expected == abstract, 'Additional abstraction mutation')
    return {'exact_whole_graph_reconstruction': True, 'reset_bits': len(substitutions),
            'removed_ff_cells': len(deleted), 'sliced_ff_cells': sliced,
            'preserved_native_word_projection_cells': len(protected), 'unchanged_word_lemma_cells': 119,
            'payload_anyseq_bits_per_cycle': 128, 'no_branch_or_admission_cut': True}


def main():
    info = read(PREPARED / 'summary.json')
    require(info['status'] == 'prepared_query_only' and info['accepted_optimization'] is False, 'Unexpected outcome')
    dependencies = {}
    for label in ('native_word_domain_import', 'external_rom_domain_import', 'inactive_fu_import'):
        for path, expected in info[label]['proof_dependencies_sha256'].items():
            require(dependencies.get(path, expected) == expected, 'Conflicting transitive binding')
            dependencies[path] = expected
    verify(dependencies)
    authoritative_count = len(dependencies)
    for path in PREPARED.rglob('*'):
        if path.is_file():
            dependencies[str(path)] = sha(path)
    for name in ('inactive_fu_import.py', 'formal_screen.py', 'domain_lemmas.py', 'rom_domain_import.py',
                 'certified_decoder.py', 'abstract_datapath.py'):
        dependencies[str(APP / name)] = sha(APP / name)
    for previous in ('inactive_fu_lemmas_v1', 'eu_register_lemma_v1'):
        path = HERE.parent / previous / 'summary.json'
        dependencies[str(path)] = sha(path)
    for name, field in [('formal_screen.py', 'script_sha256'), ('core.json', 'core_json_sha256'),
                        ('core.v', 'core_sha256'), ('AdmissionScreen.sv', 'harness_sha256'),
                        ('source.json', 'source_json_sha256'), ('screen.aig', 'aig_sha256')]:
        require(sha(PREPARED / name) == info[field], 'Prepared artifact binding changed: ' + name)
    require(sha(APP / 'formal_screen.py') == info['script_sha256'], 'Integration source changed')
    require(sha(APP / 'inactive_fu_import.py') == sha(PREPARED / 'inactive_fu_theorems/importer_source.py'), 'Importer snapshot changed')
    for name in ('core.json', 'core.v', 'AdmissionScreen.sv', 'lemma_core.json'):
        require(sha(PREPARED / name) == sha(PRIOR / name), 'Previously reviewed native/harness/lemma artifact changed: ' + name)
        dependencies[str(PRIOR / name)] = sha(PRIOR / name)
    native = read(PREPARED / 'core.json')
    raw_native = read(RAW / 'native_input.json')
    for alias, suffix in [('probe_insert', 'insert'), ('probe_index', 'new_idx')]:
        raw_native['modules']['datapath']['ports'][alias] = {'direction': 'output', 'bits':
            list(raw_native['modules']['datapath']['netnames']['u_backend.u_exec_stage.u_alu_unit.u_arith_rs.' + suffix]['bits'])}
    require(raw_native == native, 'Native export has more than observation ports added')
    graph = check_graph(native, read(PREPARED / 'lemma_core.json'), read(PREPARED / 'inactive_query_core.json'),
                        read(PREPARED / 'abstract_query_core.json'), info)
    required = info['inactive_fu_import']['proof_dependencies_sha256']
    word_map = info['native_word_domain_import']['proof_dependencies_sha256']
    require(all(word_map.get(path) == value for path, value in required.items()), 'Existing solvers would miss inactive dependency')
    for directory in (RAW, BUILD / 'eu_register_lemma_v1', BUILD / 'eu_domain_diagnostic_v1'):
        require(all(str(path) in required for path in directory.rglob('*') if path.is_file()), 'Missing nested raw artifact')
    for key, record in info['inactive_fu_import']['row_export_replays'].items():
        require(record['solver_rerun'] is False and record['properties'] == {'assert': 1, 'assume': 2, 'cover': 0}, 'Unsupported replay')
        positive = RAW / (key.replace('mul_', 'mul_row_').replace('div_', 'div_row_')) / 'positive'
        replay = PREPARED / 'inactive_fu_theorems' / positive.parent.name
        require(read(replay / 'lowered.json') == read(positive / 'lowered.json'), 'Replayed row graph changed')
        require(sha(replay / 'model.smt2') == sha(positive / 'model.smt2') == record['smt_sha256'], 'Replayed row SMT changed')
    model = read(PREPARED / 'screen.json')['modules']['AdmissionScreen']
    properties = {kind: sum(c['type'] == '$' + kind for c in model['cells'].values()) for kind in ('assert', 'assume', 'cover')}
    require(properties == info['query_property_counts'] == {'assert': 3, 'assume': 8, 'cover': 0}, 'Changed obligation inventory')
    require(not any(bit in ('x', 'z') for c in model['cells'].values() for bs in c['connections'].values() for bit in bs), 'Undefined proof literal')
    require(not any('init' in n.get('attributes', {}) for n in model['netnames'].values()), 'Unexpected initial-state constraint')
    script = (PREPARED / 'prepare.ys').read_text()
    require(script.index('setundef -anyseq') < script.index('prep -top'), 'Undefined values symbolized too late')
    require('select -assert-count 3 t:$assert' in script and 'select -assert-count 8 t:$assume' in script, 'Property count checks absent')
    for key in ('prepare', 'export'):
        require(info[key]['returncode'] == 0 and not info[key]['timeout'] and sha(info[key]['log']) == info[key]['log_sha256'], 'Preparation failed or changed')
    dependencies[str(Path(__file__))] = sha(Path(__file__))
    verify(dependencies)
    result = {'status': 'independent_inactive_fu_import_integration_review_passed', 'new_solver_queries': 0,
              'prepared_query_only': True, 'accepted_optimization': False, 'graph_checks': graph,
              'native_core_json_sha256': info['core_json_sha256'], 'harness_sha256': info['harness_sha256'],
              'prepared_query_summary_sha256': sha(PREPARED / 'summary.json'),
              'query_core_sha256': info['query_core_sha256'], 'lowered_screen_sha256': sha(PREPARED / 'screen.json'),
              'query_properties': properties, 'source_and_proof_dependency_count': authoritative_count,
              'all_transitive_dependencies_unchanged_before_after': True, 'source_sha256': dependencies,
              'native_export_and_full_harness_identical_to_prior': True, 'new_environmental_or_internal_premises': [],
              'composition': 'The exact producer theorem proves the reset-qualified response-word premise for arbitrary core outputs. Native six-word plus decoder-input invariants and decoder equivalence transfer that domain. Program-only EU/dispatch/insertion and eight row inductions discharge 1761 reset constants. The seven existing word assumptions remain identical. Fresh ALU/MUL result choices then overapproximate this closed model, so every original constrained trace remains represented.',
              'verdict': 'No blocker. The frozen integration imports proved facts into a separate proof model without changing the native hardware export, narrowing environmental behavior, or assuming the ALU admission goal.',
              'limits': ['This is model preparation and source/proof composition review, not an unbounded admission result or an area claim.',
                         'The initial reset, exact immutable zero-fault instruction ROM, and declared nonfaulting arbitrary-data service remain the external model.',
                         'Optional payload abstraction can introduce spurious counterexamples.',
                         'The inherited ROM importer checks duplicate packaged solver logs at import; its post-query map binds their authoritative originals rather than the two duplicate copies. This does not leave the theorem outcome unbound.']}
    (HERE / 'summary.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: result[key] for key in ('status', 'new_solver_queries', 'source_and_proof_dependency_count', 'query_properties')}))


if __name__ == '__main__':
    main()
