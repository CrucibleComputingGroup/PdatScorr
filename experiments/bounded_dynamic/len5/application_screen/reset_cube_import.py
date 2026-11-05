"""Replay a closed reset cube and apply only its delta to a current query.

The current query retains its register-status facts, all47 proved predicates,
native probes, and native arithmetic. No solver or hardware export is run.
"""
from __future__ import annotations
import copy
import json
from pathlib import Path

import reset_cube as cube
import reset_cube_fixedpoint as fixed
from domain_lemmas import _add_domain_assumptions
from register_status_import import fresh_rd_predicates
from register_status_lemmas import reset_substitution
from register_status_prepared import validate_register_status_prepared
from reset_cube import digest, read, require, quoted

HERE = Path(__file__).resolve().parent
SOURCE_SHA = 'bb52d686f974809e0bebd4e2b373414ec9a53af34cff5a6a48d1e5ab2465307b'
PATCH_SHA = '6192d7a41d51a0e11e8e4bb2b13128fc767ba7e4061cce27612ef7ee727e2323'
STATUSES = {'native_word_domain_import': 'seven_proved_native_word_domains_imported',
            'external_rom_domain_import': 'exact_external_rom_domain_certified',
            'inactive_fu_import': 'inactive_fu_reset_facts_replayed',
            'register_status_import': 'forty_rd_domains_and_register_status_facts_imported'}


def canonical(value):
    return json.loads(json.dumps(value))


def verify_dependencies(record):
    for path, expected in record['proof_dependencies_sha256'].items():
        require(digest(Path(path)) == expected, 'Reset-cube import dependency changed: ' + path)


def reconstruct_current(source, current, prepared):
    """Bind the intervening275 constants,479 encoding cells, and two probes."""
    words, status = prepared['native_word_domain_import'], prepared['register_status_import']
    local = read(Path(status['local_run'])/'summary.json')
    require(digest(Path(status['local_run'])/'summary.json') == status['local_summary_sha256'], 'Register-status source changed')
    rebuilt, added = _add_domain_assumptions(source, words['lemmas'],
                                            {int(value, 16) for value in words['allowed_words']})
    require(added == words['added_cells'] and len(added) == 119, 'Original seven-word encoding changed')
    module = rebuilt['modules']['datapath']
    for alias, name in (('probe_insert', 'insert'), ('probe_index', 'new_idx')):
        require(alias not in module['ports'], 'Unexpected source observation port')
        module['ports'][alias] = {'direction': 'output', 'bits':
            list(module['netnames']['u_backend.u_exec_stage.u_alu_unit.u_arith_rs.'+name]['bits'])}
    rebuilt, patch = reset_substitution(rebuilt, local['native_component_audit'])
    require(canonical(patch) == status['composition']['reset_substitution'] == local['reset_substitution'],
            'Intervening register-status constants changed')
    rebuilt, encoding = fresh_rd_predicates(rebuilt, local['rd_theorem_chain']['unique_stored_field_lemmas'],
                                            local['rd_theorem_chain']['rd_values'])
    require(encoding == status['composition']['rd_encoding'] and len(encoding['added_cells']) == 360,
            'Forty RD conclusions changed')
    require(rebuilt == current, 'Current graph is not the exact closed source plus register-status/predicate/probe changes')
    return patch, added+encoding['added_cells']


def compose_delta(source, current, rows, prepared):
    register_patch, predicates = reconstruct_current(source, current, prepared)
    cube_bits = {bit for row in rows for bit in row['q']}
    register_bits = {int(bit) for bit in register_patch['constant_substitutions']}
    inactive_bits = {int(bit) for bit in prepared['inactive_fu_import']['reset_substitutions']}
    require(len(cube_bits) == 583 and len(register_bits) == 275 and
            not cube_bits & (register_bits | inactive_bits), 'Cube overlaps earlier proved constants')
    a = current['modules']['datapath']
    for row in rows:
        require(a['cells'].get(row['name']) == row['cell'], 'Current query changed a selected native FF word')
    for name in predicates:
        require(not any(cube_bits & set(bits) for bits in a['cells'][name]['connections'].values()),
                'Cube overlaps an existing derived predicate')
    result, patch = fixed.patch_constants(current, 'datapath', rows)
    graph = fixed.audit_patch(current, result, 'datapath', patch)
    b = result['modules']['datapath']
    require(all(a['cells'][name] == b['cells'][name] for name in predicates), 'Existing proved predicate mutated')
    require(a['ports'] == b['ports'], 'Native/probe observation ports changed')
    counts = {kind: sum(c['type'] == '$'+kind for c in b['cells'].values()) for kind in ('assert', 'assume', 'cover')}
    require(counts == {'assert': 0, 'assume': 47, 'cover': 0}, 'Existing query obligation inventory changed')
    arbiters = [row for row in rows if '.u_cdb_sel.rem_valid_q' in row['name']]
    require(len(arbiters) == 2 and sum(row['width'] for row in arbiters) == 8,
            'Expected eight MUL/DIV CDB-arbiter state bits')
    for row in arbiters:
        require(row['name'] not in b['cells'], 'Retained CDB-arbiter FF was not removed')
        alias = row['name'].removeprefix('$driver$')
        require(b['netnames'][alias]['bits'] == row['reset_value'], 'CDB-arbiter aliases did not receive proved constants')
    return result, {'graph_audit': graph, 'constant_substitutions': patch['constant_substitutions'],
        'existing_predicate_cells_preserved': predicates, 'existing_proved_assumptions_preserved': 47,
        'preceding_register_status_constants_preserved': 275, 'native_and_probe_ports_unchanged': True,
        'cdb_arbitration_bits_substituted': [bit for row in arbiters for bit in row['q']],
        'proof_only_property_counts': counts}


def replay_obligation(source, rows, run, out, mode, proof, yosys):
    """Only reproduce the two export stages; never execute the SAT command."""
    old = run/f'final_{mode}'
    out.mkdir()
    projection, audit = cube.project(source, 'datapath', rows, mode=mode)
    require(projection == read(old/'projection.json') and canonical(audit) == read(old/'projection_audit.json'),
            'Proved cube projection differs from original native cells')
    require(audit['reset_base_premise'] == ({'rst_ni': 0} if mode == 'base' else None), 'Changed reset-base premise')
    require(len(audit['hypothesis_q_constants']) == (583 if mode == 'induction' else 0), 'Changed simultaneous induction cube')
    first = f'read_json {quoted(old/"projection.json")}\nsetundef -anyseq\nbwmuxmap\nbmuxmap\ndemuxmap\nsetundef -anyseq\n'
    first += f'write_json {quoted(old/"symbolized_before_prep.json")}\n'
    second = f'read_json {quoted(old/"binary_inputs_before_prep.json")}\nprep -top ResetCube\nsetundef -anyseq\ncheck -assert\n'
    second += f'write_json {quoted(old/"normalized_symbolic.json")}\n'
    require((old/'symbolize/run.ys').read_text() == first and (old/'execution/run.ys').read_text() == second,
            'Cube proof export pipeline changed')
    executions = []
    script = first.replace(quoted(old/'symbolized_before_prep.json'), quoted(out/'symbolized_before_prep.json'))
    execution = cube.execute(script, out/'symbolize', yosys, 30)
    require(execution['returncode'] == 0 and not execution['timeout'], 'Cube symbolization replay failed')
    executions.append(execution)
    require(digest(out/'symbolized_before_prep.json') == digest(old/'symbolized_before_prep.json'), 'Symbolized cube model changed')
    binary, before_choices = cube.expose_choices(read(out/'symbolized_before_prep.json'))
    (out/'binary_inputs_before_prep.json').write_text(json.dumps(binary)+'\n')
    require(digest(out/'binary_inputs_before_prep.json') == digest(old/'binary_inputs_before_prep.json'), 'Binary choice exposure changed')
    script = second.replace(quoted(old/'binary_inputs_before_prep.json'), quoted(out/'binary_inputs_before_prep.json'))
    script = script.replace(quoted(old/'normalized_symbolic.json'), quoted(out/'normalized_symbolic.json'))
    execution = cube.execute(script, out/'execution', yosys, 30)
    require(execution['returncode'] == 0 and not execution['timeout'], 'Cube normalization replay failed')
    executions.append(execution)
    require(digest(out/'normalized_symbolic.json') == digest(old/'normalized_symbolic.json'), 'Normalized cube model changed')
    lowered, after_choices = cube.expose_choices(read(out/'normalized_symbolic.json'))
    (out/'lowered.json').write_text(json.dumps(lowered)+'\n')
    require(digest(out/'lowered.json') == digest(old/'lowered.json') == proof['lowered_sha256'], 'Final SAT model changed')
    require(proof['binary_choice_exposure']['before_prep'] == before_choices and
            proof['binary_choice_exposure']['after_prep'] == after_choices, 'Symbolic-choice binding changed')
    sat = f'read_json {quoted(old/"lowered.json")}\ncheck -assert\n'
    reset_arg = ' -set rst_ni 0' if mode == 'base' else ''
    sat += f'tee -o {quoted(old/"sat.log")} sat -set-def-inputs{reset_arg} -prove cube_bad 0 -show-ports -dump_json {quoted(old/"counterexample.json")}\n'
    require((old/'sat_execution/run.ys').read_text() == sat, 'SAT premise or target changed')
    for execution in (proof['symbolize_execution'], proof['execution'], proof['sat_execution']):
        script = Path(execution['argv'][-1])
        require(execution['returncode'] == 0 and not execution['timeout'] and digest(script) == execution['script_sha256'] and
                digest(script.parent/'run.log') == execution['log_sha256'], 'Original proof execution is not intact')
    log = (old/'sat.log').read_text()
    require(proof['status'] == 'proved_combinationally' and digest(old/'sat.log') == proof['sat_log_sha256'] and
            log.count('SAT proof finished - no model found: SUCCESS!') == 1 and
            'SAT proof finished - model found: FAIL!' not in log, 'Missing explicit final SAT proof')
    module = lowered['modules']['ResetCube']
    require(not any(cube.state_cell(c) or c['type'] in cube.FORBIDDEN | {'$anyseq', '$anyconst'} for c in module['cells'].values()),
            'Hidden state or premise in final one-step model')
    require(not any(bit in ('x','z') for c in module['cells'].values() for bits in c['connections'].values() for bit in bits),
            'Undefined literal in final proof model')
    return {'mode': mode, 'export_replays': executions, 'model_sha256': proof['lowered_sha256'],
            'original_sat_log_sha256': proof['sat_log_sha256'], 'byte_identical': True, 'solver_rerun': False}


def import_reset_cube(run, reference_prepared, current, out, *, yosys, current_records,
                      current_harness, current_native_core, review_path=None):
    run, reference_prepared, out = map(lambda p: Path(p).resolve(), (run, reference_prepared, out))
    review_path = Path(review_path or HERE/'review/reset_cube_fixedpoint_v1/review.json').resolve()
    review = read(review_path)
    require(review['status'] == 'independent_reset_cube_source_semantics_and_artifact_review_passed' and
            review['input_prior_query_sha256'] == SOURCE_SHA and review['patch_sha256'] == PATCH_SHA,
            'Closed independent cube review is required')
    prepared = validate_register_status_prepared(reference_prepared)
    require(current == read(Path(prepared['query_core_path'])), 'Current query differs from the validated48-premise reference')
    require(digest(current_harness) == prepared['harness_sha256'] and digest(current_native_core) == prepared['core_json_sha256'],
            'Current native export or environmental/observation harness changed')
    info = read(run/'summary.json')
    require(info['status'] == 'reset_cube_certified_query_patch_only' and info['accepted_optimization'] is False and
            info['query_only'] and info['new_environmental_premises'] == [] and
            info['certified_words'] == 42 and info['certified_bits'] == 583, 'Cube is not a closed query-only certificate')
    require(digest(run/'source.json') == info['source_sha256'] == SOURCE_SHA and
            digest(run/'query_only_patch.json') == info['query_only_patch_sha256'] == PATCH_SHA, 'Cube native source or delta changed')
    dependencies = {}
    def bind(path, expected=None):
        path = Path(path).resolve()
        value = digest(path)
        require(expected is None or value == expected, 'Proof dependency changed before import: ' + str(path))
        require(dependencies.get(str(path), value) == value, 'Conflicting source binding')
        dependencies[str(path)] = value
    for mapping in (info['dependencies_sha256'], review['source_sha256']):
        for path, value in mapping.items(): bind(path, value)
    require(set(current_records) == set(STATUSES), 'All current proof-chain records are required')
    for key, expected_status in STATUSES.items():
        for record in (prepared[key], current_records[key]):
            require(record['status'] == expected_status, 'Current proof chain is not closed: ' + key)
            for path, value in record['proof_dependencies_sha256'].items(): bind(path, value)
    for root in (run, reference_prepared, review_path.parent):
        for path in root.rglob('*'):
            if path.is_file() and '__pycache__' not in path.parts: bind(path)
    for path in (Path(__file__), Path(cube.__file__), Path(fixed.__file__), current_harness, current_native_core,
                 HERE/'register_status_prepared.py', HERE/'register_status_import.py', HERE/'register_status_lemmas.py',
                 HERE/'domain_lemmas.py'):
        bind(path)
    require(digest(cube.__file__) == digest(run/'reset_cube.py') and
            digest(fixed.__file__) == digest(run/'reset_cube_fixedpoint.py'), 'Frozen cube implementation changed')
    require(str(Path(yosys).resolve()) in dependencies, 'Cube export replay needs the source-bound Yosys binary')
    source, rows = read(run/'source.json'), read(run/'selected_words.json')
    eligible, _ = cube.eligibility(source, 'datapath')
    known = {row['name']: row for row in eligible}
    require(len(rows) == len({row['name'] for row in rows}) == 42 and all(known.get(row['name']) == row for row in rows),
            'Selected cube is not the exact native FF set')
    old_patch, manifest = fixed.patch_constants(source, 'datapath', rows)
    require(old_patch == read(run/'query_only_patch.json') and fixed.audit_patch(source, old_patch, 'datapath', manifest) == info['graph_audit'],
            'Recorded source cube patch differs')
    result, transport = compose_delta(source, current, rows, prepared)
    out.mkdir()
    replays = {mode: replay_obligation(source, rows, run, out/mode, mode, info['final_proofs'][mode], yosys)
               for mode in ('induction', 'base')}
    record = {'status': 'closed_reset_cube_delta_imported', 'query_only': True, 'accepted_optimization': False,
        'new_environmental_premises': [], 'new_unproved_internal_premises': 0, 'assumptions_added': 0,
        'proved_reset_words_substituted': 42, 'proved_reset_bits_substituted': 583,
        'native_hardware_export_unchanged': True, 'reference_prepared_directory': str(reference_prepared),
        'reference_summary_sha256': digest(reference_prepared/'summary.json'),
        'native_core_sha256': prepared['core_json_sha256'], 'harness_sha256': prepared['harness_sha256'],
        'cube_source_sha256': SOURCE_SHA, 'source_cube_patch_sha256': PATCH_SHA,
        'independent_review_path': str(review_path), 'independent_review_sha256': digest(review_path),
        'composition': transport, 'export_replays': replays, 'proof_dependencies_sha256': dependencies,
        'transport': 'The source-closed reset cube was proved on the prior inactive-FU property-free graph. '
            'The current query is reconstructed as exactly that graph plus the separately proved275register-status constants, '
            '47derived predicates, and unchanged native probes. The disjoint pointwise substitutions commute; added proved '
            'conclusions remove no original constrained behavior. Only the42word/583bit delta is applied to this current graph. '
            'All predicates, prior facts, probes, native arithmetic, and original safety obligations remain intact.'}
    verify_dependencies(record)
    validate_register_status_prepared(reference_prepared)
    (out/'reset_cube_import_source.py').write_bytes(Path(__file__).read_bytes())
    (out/'summary.json').write_text(json.dumps(record, indent=2)+'\n')
    return result, record
