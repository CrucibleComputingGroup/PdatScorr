"""Proof composition rejects changed producers and keeps native hardware separate."""
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
import rom_domain_import as importer
import formal_screen as screen
import solve_prepared


def test_query_only_properties_cannot_replace_hardware():
    native = {'modules': {'datapath': {'ports': {'out': {'direction':'output','bits':[3]}},
        'netnames': {}, 'cells': {'native': {'type':'$not','connections':{'A':[2],'Y':[3]}}}}}}
    query = copy.deepcopy(native)
    extra = []
    for i in range(7):
        name = f'lemma{i}'; extra.append(name)
        query['modules']['datapath']['cells'][name] = {'type':'$assume','connections':{'A':[2],'EN':['1']}}
    assert screen.validate_query_only_delta(native, query, extra) == {'assert':0,'assume':7,'cover':0}
    query['modules']['datapath']['cells']['native']['connections']['A'] = ['0']
    with pytest.raises(ValueError, match='changed native hardware'):
        screen.validate_query_only_delta(native, query, extra)


def test_native_probes_do_not_mutate_input_or_drivers():
    prefix = 'u_backend.u_exec_stage.u_alu_unit.u_arith_rs.'
    native = {'modules': {'datapath': {'ports': {}, 'cells': {}, 'netnames': {
        prefix+'insert': {'bits':[2]}, prefix+'new_idx': {'bits':[3,4,5]}}}}}
    result = screen.add_native_probes(native)
    assert not native['modules']['datapath']['ports']
    assert result['modules']['datapath']['cells'] == native['modules']['datapath']['cells']
    assert result['modules']['datapath']['ports']['probe_index']['bits'] == [3,4,5]
    with pytest.raises(ValueError, match='already exists'): screen.add_native_probes(result)


@pytest.fixture
def actual(tmp_path):
    cert = APP/'evidence/rom_domain_v2/summary.json'
    if not cert.exists(): pytest.skip('Frozen external ROM theorem unavailable')
    info = json.loads(cert.read_text()); source = Path(info['source_directory'])
    yosys = Path('/home/allenjin/Projects/DAC_pscorr/tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys')
    if not source.exists() or not yosys.exists(): pytest.skip('Frozen native source/tools unavailable')
    from program_rom import read_image
    image = read_image(source/'program.hex')
    allowed = {int(x,16) for x in info['domain_words']}
    return cert, source, image, allowed, str(yosys)


def test_actual_rom_theorem_exact_source_and_export_replay(actual, tmp_path):
    cert, source, image, allowed, yosys = actual
    record = importer.validate_rom_domain(cert, source/'AdmissionScreen.sv', source/'core.json', image,
        tmp_path/'validated', allowed_words=allowed, yosys=yosys)
    assert record['status'] == 'exact_external_rom_domain_certified'
    assert record['model_properties'] == {'assert':3,'assume':1,'cover':0}
    assert record['assumptions_added'] == 0
    importer.verify_dependencies(record)
    assert 'smtbmc' not in record['model_export_replay']['argv'][0]


@pytest.mark.parametrize('change', ['producer', 'port', 'image', 'word_domain', 'withdrawn'])
def test_changed_producer_contract_is_rejected(actual, tmp_path, monkeypatch, change):
    cert, source, image, allowed, yosys = actual
    harness, core = source/'AdmissionScreen.sv', source/'core.json'
    if change == 'producer':
        path = tmp_path/'AdmissionScreen.sv'; path.write_text(harness.read_text().replace('if (mem_flush_o)', 'if (1\'b0)'))
        harness = path
    elif change == 'port':
        path = tmp_path/'core.json'; design = json.loads(core.read_text())
        design['modules']['datapath']['ports']['instr_req_o']['bits'] = [99999999]
        path.write_text(json.dumps(design)); core = path
    elif change == 'image': image = {**image, 'image_sha256':'0'*64}
    elif change == 'word_domain': allowed = {0}
    else:
        path = tmp_path/'summary.json'; info = json.loads(cert.read_text()); info['status']='withdrawn'
        path.write_text(json.dumps(info)); cert = path
    monkeypatch.setattr(importer, 'checked_yosys', lambda *args: pytest.fail('Invalid producer reached model export'))
    with pytest.raises(ValueError):
        importer.validate_rom_domain(cert, harness, core, image, tmp_path/'rejected', allowed_words=allowed, yosys=yosys)


def test_external_proof_mutation_after_query_invalidates_result(tmp_path):
    path = tmp_path/'proof'; path.write_text('proved')
    record = {'proof_dependencies_sha256': {str(path): importer.digest(path)}}
    importer.verify_dependencies(record)
    path.write_text('changed')
    with pytest.raises(ValueError, match='dependency changed'): importer.verify_dependencies(record)


def test_solver_uses_only_unchanged_inspected_artifacts(tmp_path):
    summary = {'status':'prepared_query_only', 'accepted_optimization':False,
               'query_property_counts':{'assert':3,'assume':1,'cover':0}}
    for key, name in [('source_json','source.json'), ('core','core.v'), ('core_json','core.json'),
        ('harness','AdmissionScreen.sv'), ('script','formal_screen.py'), ('temporal_helper','temporal.py'),
        ('rom_helper','program_rom.py'), ('rom_image','program.hex'), ('aig','screen.aig')]:
        path=tmp_path/name; path.write_text(name)
        summary[key+'_sha256']=importer.digest(path)
    summary['query_core_path']=str(tmp_path/'core.json')
    summary['query_core_sha256']=importer.digest(tmp_path/'core.json')
    (tmp_path/'summary.json').write_text(json.dumps(summary))
    assert solve_prepared.validate_prepared(tmp_path)==summary
    (tmp_path/'screen.aig').write_text('changed solver obligation')
    with pytest.raises(ValueError, match='Prepared artifact changed: screen.aig'):
        solve_prepared.validate_prepared(tmp_path)


def test_bounded_result_cannot_be_relabelled_as_inspected_preparation(tmp_path):
    (tmp_path/'summary.json').write_text(json.dumps({'status':'bounded_only_no_certificate','accepted_optimization':False}))
    with pytest.raises(ValueError, match='Only an inspected preparation'):
        solve_prepared.validate_prepared(tmp_path)


def test_actual_payload_abstraction_preserves_every_certified_word_cell():
    prepared = Path('/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build/harvard_rom_word_lemmas_prepare_v1')
    if not (prepared/'lemma_core.json').exists(): pytest.skip('Frozen composed native model unavailable')
    design = json.loads((prepared/'lemma_core.json').read_text())
    record = json.loads((prepared/'summary.json').read_text())['native_word_domain_import']
    result, audit = screen.abstract_query_model(design, 'alu_mul', record)
    assert audit['fresh_symbolic_bits_per_cycle'] == 128
    assert len(audit['native_cells_removed']) == 2
    assert audit['all_certified_word_projection_and_assumption_cells_unchanged']
    a, b = design['modules']['datapath'], result['modules']['datapath']
    assert a['ports'] == b['ports'] and a['netnames'] == b['netnames']
    assert all(b['cells'][name] == cell for name,cell in a['cells'].items() if 'ff' in cell['type'].lower())
    assert all(b['cells'][name] == a['cells'][name] for name in record['added_cells'])
    collision = copy.deepcopy(record)
    collision['source_projection_preserved_control_cells'].append(audit['native_cells_removed'][0])
    with pytest.raises(ValueError, match='intersects certified'):
        screen.abstract_query_model(design, 'alu_mul', collision)
    branch, branch_audit = screen.abstract_query_model(design, 'alu_mul_branch_taken', record)
    assert branch_audit['fresh_symbolic_bits_per_cycle'] == 129
    assert len(branch_audit['native_cells_removed']) == 3
    assert branch_audit['cuts'][2]['target'] == 'branch_taken' and branch_audit['cuts'][2]['width'] == 1
    b = branch['modules']['datapath']
    assert all(b['cells'][name] == cell for name,cell in a['cells'].items() if 'ff' in cell['type'].lower())
    assert all(b['cells'][name] == a['cells'][name] for name in record['added_cells'])
    collision = copy.deepcopy(record)
    collision['source_projection_preserved_control_cells'].append(branch_audit['native_cells_removed'][2])
    with pytest.raises(ValueError, match='intersects certified'):
        screen.abstract_query_model(design, 'alu_mul_branch_taken', collision)
