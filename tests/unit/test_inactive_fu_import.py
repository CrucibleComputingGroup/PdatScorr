"""Closed inactive-FU composition; tiny export replays run no solver queries."""
import copy
import json
from pathlib import Path
import sys

import pytest

ROOT=Path(__file__).resolve().parents[2]
APP=ROOT/'experiments/bounded_dynamic/len5/application_screen'
sys.path[:0]=[str(ROOT),str(APP)]
import inactive_fu_import as importer
import formal_screen

BUILD=Path('/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build')
YOSYS='/home/allenjin/Projects/DAC_pscorr/tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys'


@pytest.fixture
def actual():
    run=BUILD/'inactive_fu_lemmas_v1';prepared=BUILD/'harvard_rom_word_lemmas_alu_mul_prepare_v1'
    if not (run/'summary.json').exists() or not Path(YOSYS).exists():pytest.skip('Frozen native proofs unavailable')
    data=json.loads((prepared/'summary.json').read_text())
    native=json.loads((run/'native_input.json').read_text())
    certificate=ROOT/'experiments/bounded_dynamic/len5/isa_baseline/results/program_alphabet_certificate_v3.json'
    return run,prepared,data,native,certificate


def test_actual_closed_substitution_replays_all_eight_models_and_preserves_lemmas(actual,tmp_path):
    run,prepared,data,native,certificate=actual
    reduced,record=importer.import_inactive_facts(run,certificate,native,
        BUILD/'pre_fpu_frontend/source/rtl/expipe/exec-units/arith_rs.sv',tmp_path/'import',yosys=YOSYS,
        dependency_records=(data['native_word_domain_import'],data['external_rom_domain_import']))
    assert record['assumptions_added']==0 and record['graph_audit']['reset_bits']==1761
    assert len(record['row_export_replays'])==8
    assert all(replay['solver_rerun'] is False and 'smtbmc' not in replay['execution']['argv'][0]
               for replay in record['row_export_replays'].values())
    before=json.loads((prepared/'lemma_core.json').read_text())
    query=formal_screen.compose_inactive_query(native,before,reduced,data['native_word_domain_import'],record)
    for name in data['native_word_domain_import']['added_cells']:
        assert query['modules']['datapath']['cells'][name]==before['modules']['datapath']['cells'][name]
    assert sum(c['type']=='$assume' for c in query['modules']['datapath']['cells'].values())==7
    assert json.loads((run/'native_input.json').read_text())==native
    importer.verify_dependencies(record)
    assert any(path.endswith('div_row_3/positive/model.smt2') for path in record['proof_dependencies_sha256'])
    assert any(path.endswith('candidate_unrestricted/sat.log') for path in record['proof_dependencies_sha256'])


def test_missing_external_closure_is_rejected(actual,tmp_path,monkeypatch):
    run,_,data,native,certificate=actual
    monkeypatch.setattr(importer.generator,'validate_eu_chain',lambda *args:pytest.fail('Unclosed context reached theorem replay'))
    with pytest.raises(ValueError,match='external-ROM theorem'):
        importer.import_inactive_facts(run,certificate,native,BUILD/'pre_fpu_frontend/source/rtl/expipe/exec-units/arith_rs.sv',
            tmp_path/'rejected',yosys=YOSYS,dependency_records=(data['native_word_domain_import'],))


def test_changed_native_input_rejected_before_proof_replay(actual,tmp_path,monkeypatch):
    run,_,data,native,certificate=actual
    native=copy.deepcopy(native);native['modules']['datapath']['ports']['clk_i']['bits']=[99999999]
    monkeypatch.setattr(importer.generator,'validate_eu_chain',lambda *args:pytest.fail('Wrong source reached theorem replay'))
    with pytest.raises(ValueError,match='different native candidate'):
        importer.import_inactive_facts(run,certificate,native,BUILD/'pre_fpu_frontend/source/rtl/expipe/exec-units/arith_rs.sv',
            tmp_path/'rejected',yosys=YOSYS,dependency_records=(data['native_word_domain_import'],data['external_rom_domain_import']))


def test_transitive_proof_mutation_invalidates_result(tmp_path):
    proof=tmp_path/'nested_induction.log';proof.write_text('passed')
    record={'proof_dependencies_sha256':{str(proof):importer.digest(proof)}}
    importer.verify_dependencies(record);proof.write_text('changed')
    with pytest.raises(ValueError,match='dependency changed'):importer.verify_dependencies(record)


def test_word_lemma_overlap_is_rejected(actual):
    run,prepared,data,native,_=actual
    before=json.loads((prepared/'lemma_core.json').read_text());reduced=json.loads((run/'query_only.json').read_text())
    word=data['native_word_domain_import'];first=before['modules']['datapath']['cells'][word['added_cells'][0]]
    bit=next(x for x in first['connections']['A'] if type(x)is int)
    with pytest.raises(ValueError,match='overlaps a certified word lemma'):
        formal_screen.compose_inactive_query(native,before,reduced,word,{'reset_substitutions':{str(bit):'0'}})
