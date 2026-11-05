"""Fail-closed theorem imports; synthetic structural fixtures are not proofs."""
import copy
import importlib.util
import json
from pathlib import Path
import shutil
import sys

import pytest

ROOT = Path(__file__).resolve().parents[2]
APP = ROOT/'experiments/bounded_dynamic/len5/application_screen'
sys.path[:0] = [str(ROOT), str(APP)]
spec = importlib.util.spec_from_file_location('domain_lemmas', APP/'domain_lemmas.py')
module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)


@pytest.fixture
def native_fixture():
    ports = {'clk_i': {'direction': 'input', 'bits': [2]}, 'rst_ni': {'direction': 'input', 'bits': [3]},
             'instr_rvalid_i': {'direction': 'input', 'bits': [4]},
             'instr_rdata_i': {'direction': 'input', 'bits': list(range(10, 42))}}
    cells = {}; state = []
    for i in range(6):
        bits = list(range(100+32*i, 132+32*i)); name = f'word{i}'
        cells[name] = {'type': '$adff', 'parameters': {'WIDTH': format(32, '032b'), 'CLK_POLARITY': 1,
            'ARST_POLARITY': 0, 'ARST_VALUE': '0'*32}, 'attributes': {}, 'hide_name': 0,
            'port_directions': {'CLK': 'input', 'ARST': 'input', 'D': 'input', 'Q': 'output'},
            'connections': {'CLK': [2], 'ARST': [3], 'D': ports['instr_rdata_i']['bits'], 'Q': bits}}
        state.append({'cell': name, 'bits': bits, 'original_indices': list(range(32))})
    cells['control'] = {'type': '$not', 'parameters': {'A_WIDTH': 1, 'Y_WIDTH': 1, 'A_SIGNED': 0},
        'attributes': {}, 'hide_name': 0, 'port_directions': {'A': 'input', 'Y': 'output'}, 'connections': {'A': [4], 'Y': [500]}}
    original = {'modules': {'datapath': {'ports': ports, 'cells': cells,
        'netnames': {module.TARGET: {'bits': state[0]['bits']}}}}}
    projected_ports = {key: copy.deepcopy(ports[native]) for key, native in
        [('clk_i', 'clk_i'), ('rst_ni', 'rst_ni'), ('instruction_i', 'instr_rdata_i'), ('response_valid', 'instr_rvalid_i')]}
    projected_ports['decoder_word'] = {'direction': 'output', 'bits': state[0]['bits']}
    for i, word in enumerate(state): projected_ports[f'state_word_{i}'] = {'direction': 'output', 'bits': word['bits']}
    projected = {'modules': {'InstructionDataPath': {'ports': projected_ports, 'cells': copy.deepcopy(cells), 'netnames': {}}}}
    audit = {'target_net': module.TARGET, 'target_width': 32, 'internal_assumptions_added': 0,
        'original_cell_slices': {w['cell']: w['original_indices'] for w in state},
        'retained_spill_write_control_cells': ['control'], 'state_words': state}
    return original, projected, audit


def test_exact_state_and_decoder_bindings_preserve_all_native_drivers(native_fixture):
    original, projection, audit = native_fixture; before = copy.deepcopy(original)
    bindings = module.native_lemma_bindings(original, original, projection, audit)
    result, added = module._add_domain_assumptions(original, bindings, {0, 0x6f})
    assert len(bindings) == 7 and len(added) == 28 and original == before
    a, b = original['modules']['datapath'], result['modules']['datapath']
    assert a['ports'] == b['ports'] and a['netnames'] == b['netnames']
    assert all(b['cells'][name] == cell for name, cell in a['cells'].items())
    assert sum(cell['type'] == '$assume' for cell in b['cells'].values()) == 7
    assert all(b['cells'][name]['type'] in ('$eq', '$reduce_or', '$assume') for name in added)


@pytest.mark.parametrize('change', ['q_bit', 'wrong_cell', 'missing_word', 'extra_output', 'native_data', 'native_control', 'reset_polarity'])
def test_changed_source_slices_or_controls_are_rejected(native_fixture, change):
    original, projection, audit = copy.deepcopy(native_fixture); target = copy.deepcopy(original)
    if change == 'q_bit': audit['state_words'][0]['bits'][0] = 999
    elif change == 'wrong_cell': audit['state_words'][0]['cell'] = 'control'
    elif change == 'missing_word': audit['state_words'].pop()
    elif change == 'extra_output': projection['modules']['InstructionDataPath']['ports']['readiness'] = {'direction': 'output', 'bits': [500]}
    elif change == 'native_data': target['modules']['datapath']['cells']['word0']['connections']['D'][0] = '1'
    elif change == 'native_control': target['modules']['datapath']['cells']['control']['connections']['A'] = ['1']
    else: original['modules']['datapath']['cells']['word0']['parameters']['ARST_POLARITY'] = 1
    with pytest.raises((ValueError, KeyError)): module.native_lemma_bindings(original, target, projection, audit)


def test_assumption_truth_table_rejects_only_nonmembers(native_fixture):
    original, projection, audit = native_fixture
    binding = module.native_lemma_bindings(original, original, projection, audit)[0]
    result, added = module._add_domain_assumptions(original, [binding], {0, 0x6f})
    cells = result['modules']['datapath']['cells']
    for value, expected in [(0, True), (0x6f, True), (0x13, False), (0xffffffff, False)]:
        env = {bit: bool((value >> i) & 1) for i, bit in enumerate(binding['bits'])}
        decisions = []
        def bits(v): return sum((int(x) if isinstance(x, str) else int(env[x])) << i for i, x in enumerate(v))
        for name in added:
            c = cells[name]; con = c['connections']
            if c['type'] == '$eq': env[con['Y'][0]] = bits(con['A']) == bits(con['B'])
            elif c['type'] == '$reduce_or': env[con['Y'][0]] = bits(con['A']) != 0
            else: decisions.append(bool(bits(con['A'])) and bits(con['EN']) == 1)
        assert decisions == [expected]


def test_mutation_after_import_invalidates_evidence(tmp_path):
    source = tmp_path/'source'; source.write_text('frozen')
    record = {'proof_dependencies_sha256': {str(source): module.digest(source)}}
    module.verify_dependencies(record)
    source.write_text('changed')
    with pytest.raises(ValueError, match='dependency changed'): module.verify_dependencies(record)


def test_export_replay_rejects_injected_premise_before_yosys(tmp_path, monkeypatch):
    (tmp_path/'export.ys').write_text('read_json "unexpected.json"\nchformal -assert -assume\n')
    monkeypatch.setattr(module, 'checked_yosys', lambda *args: pytest.fail('Unsafe script reached Yosys'))
    with pytest.raises(ValueError, match='changed domain export'): module.replay_domain_export(tmp_path, tmp_path/'fresh', 'unused', 1)


def test_bounded_pass_cannot_be_imported_as_an_unbounded_lemma(tmp_path):
    log = tmp_path/'bounded.log'; log.write_text('Status: PASSED\n')
    run = {'returncode': 0, 'timeout': False, 'log': str(log), 'log_sha256': module.digest(log),
           'argv': ['yosys-smtbmc', str(tmp_path/'model.smt2')]}
    summary = {'status': 'proved', 'base': run, 'induction': copy.deepcopy(run)}
    with pytest.raises(ValueError, match='Bounded checks'): module.check_unbounded_domain_proof(summary, tmp_path)
    summary['induction']['argv'].insert(1, '-i')
    with pytest.raises(ValueError, match='Missing unbounded'): module.check_unbounded_domain_proof(summary, tmp_path)


def test_actual_frozen_certificate_replays_without_running_solver(tmp_path):
    """Integration uses existing proved data; only the small Yosys model export reruns."""
    cert = ROOT/'experiments/bounded_dynamic/len5/isa_baseline/results/program_alphabet_certificate_v3.json'
    if not cert.exists(): pytest.skip('Frozen native certificate unavailable')
    info = json.loads(cert.read_text()); source = Path(info['native_original_json'])
    yosys = Path('/home/allenjin/Projects/DAC_pscorr/tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys')
    if not source.exists() or not yosys.exists(): pytest.skip('External native proof artifacts/tools unavailable')
    original = json.loads(source.read_text()); before = module.digest(source)
    # This tiny ROM is within the same theorem domain; no program behavior is assumed.
    image = {'bytes': 4, 'words': {0: 0x6f}, 'immutable_instruction_image': True,
             'byte_order': 'little', 'image_sha256': 'unit-test-ROM-domain-only'}
    design, record = module.import_word_domain_lemmas(cert, source, original, image, tmp_path/'import',
        certifier=cert.parent.parent/'certify.py', yosys=str(yosys), zero_fault_data=True, initial_reset=True)
    assert record['assumptions_added'] == 7 and record['new_unproved_internal_premises'] == 0
    assert record['accepted_optimization'] is False and module.digest(source) == before
    assert record['proved_domain_model_properties'] == {'assert': 7, 'assume': 2, 'cover': 0}
    assert len(record['source_projection_preserved_control_cells']) == 36
    assert sum(c['type'] == '$assume' for c in design['modules']['datapath']['cells'].values()) == 7
    assert any(path.endswith('model.smt2') for path in record['proof_dependencies_sha256'])
    module.verify_dependencies(record)
    assert 'smtbmc' not in record['domain_export_replay']['argv'][0]
