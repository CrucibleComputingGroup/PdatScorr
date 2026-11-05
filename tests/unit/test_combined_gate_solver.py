"""Expanded constraint qualification and fail-closed combined GLA wrapper."""
import copy
import json
from pathlib import Path
import sys
import pytest

ROOT=Path(__file__).resolve().parents[2]
APP=ROOT/'experiments/bounded_dynamic/len5/application_screen'
sys.path[:0]=[str(ROOT),str(APP)]
import combined_gate_solver as driver


@pytest.fixture
def model(tmp_path,monkeypatch):
    proof=tmp_path/'proof.log';proof.write_text('proved')
    deps={str(proof):driver.digest(proof)}
    record=dict(abstraction_mode='none',datapath_abstraction=None,
        query_property_counts={'assert':3,'assume':48,'cover':0},instruction_model='immutable_rom',
        instruction_fault_payload='zero',query_core_path=str(tmp_path/'reset_cube_query_core.json'),
        core_json_sha256='native',query_core_sha256='query',aig_sha256='aig')
    for name in driver.RECORDS:record[name]={'proof_dependencies_sha256':deps.copy()}
    (tmp_path/'summary.json').write_text(json.dumps(record))
    monkeypatch.setattr(driver.reset_cube_prepared,'validate_reset_cube_prepared',lambda _:copy.deepcopy(record))
    return tmp_path,record,proof


@pytest.mark.parametrize('mutation,match',[
    (lambda r:r.update(abstraction_mode='alu_mul'),'Native arithmetic'),
    (lambda r:r['query_property_counts'].update(assume=49),'three assertions'),
    (lambda r:r.update(instruction_fault_payload='arbitrary'),'zero-fault'),
    (lambda r:r.update(query_core_path='/tmp/other'),'combined cube'),
    (lambda r:r['native_word_domain_import'].update(proof_dependencies_sha256={}),'Incomplete transitive'),
])
def test_reject_scope_changes(model,mutation,match):
    path,record,_=model;mutation(record)
    with pytest.raises(ValueError,match=match):driver.validate_combined(path)


def test_changed_transitive_dependency_rejected(model):
    path,_,proof=model;proof.write_text('changed')
    with pytest.raises(ValueError,match='dependency changed'):driver.validate_combined(path)


@pytest.mark.parametrize('change',[False,True])
def test_postrun_guard_rejects_changed_dependency(model,monkeypatch,change):
    path,_,proof=model
    def qualify(output,**kwargs):
        output.mkdir();record={'status':'qualified','artifacts_sha256':{}}
        (output/'summary.json').write_text(json.dumps(record));return record
    def run(aig,output,**kwargs):
        output.mkdir();(output/'summary.json').write_text('{}')
        if change:proof.write_text('changed during target')
        return {'status':'unknown','input_aig_sha256':'aig'}
    monkeypatch.setattr(driver,'qualify_48',qualify)
    monkeypatch.setattr(driver.gate_solver,'run_gla',run)
    result=driver.run_combined(path,path/'run',timeout=1,abc=sys.executable,yosys=sys.executable)
    assert result['status']==('error' if change else 'unknown')
    assert result['post_run_dependencies_verified'] is not change
    assert (path/'run/wrapper_sources/combined_gate_solver.py').exists()


def test_real48constraints_and_missing_last_counterexample(tmp_path):
    if not Path(driver.YOSYS).exists() or not Path('/usr/local/bin/abc').exists():pytest.skip('Pinned tools unavailable')
    record=driver.qualify_48(tmp_path/'qualification')
    assert record['status']=='qualified'
    positive=record['cases']['all48'];negative=record['cases']['without_last']
    assert int(positive['preparation']['aig_header'][7])==48
    assert int(negative['preparation']['aig_header'][7])==47
    assert positive['result']['status']=='proved_safety_query_only'
    assert negative['result']['status']=='counterexample_in_query_model'
    assert (tmp_path/'qualification/without_last_gla/counterexample.aiw').exists()


def test_actual_combined_model_and_transitive_closure():
    path=Path('/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build/harvard_rom_register_status_cube_native_prepare_v1')
    if not path.exists():pytest.skip('External prepared model unavailable')
    record,deps=driver.validate_combined(path)
    assert len(deps)==2329
    assert record['aig_header'][3:6]==['21741','0','515078']
