"""Fail-closed native GLA-map import and bounded-search orchestration."""
import copy
import json
from pathlib import Path
import sys

import pytest

ROOT=Path(__file__).resolve().parents[2]
APP=ROOT/'experiments/bounded_dynamic/len5/application_screen'
sys.path[:0]=[str(ROOT),str(APP)]
import native_gate_bmc as driver

GLA=Path('/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build/harvard_rom_inactive_fu_native_gla_v1')


def test_actual_native_map_and_complete_dependencies():
    if not GLA.exists():pytest.skip('External source-bound native GLA run unavailable')
    info, model, deps=driver.validate_native_gla(GLA)
    assert info['abstracted_header']==['aig','15559','1581','684','1','13294']
    assert model['abstraction_mode']=='none'
    assert len(deps)>269
    assert str(GLA/'final_map.aig') in deps


@pytest.mark.parametrize('frames,timeout',[(129,120),(128,121),(0,120),(128,0)])
def test_budget_rejected_before_reading_source(tmp_path,frames,timeout):
    with pytest.raises(ValueError,match='budget'):
        driver.run_native_bmc(tmp_path/'missing',tmp_path/'run',frames=frames,timeout=timeout)


@pytest.mark.parametrize('mutation,match',[
    (lambda d:d.update(abstraction_mode='alu_mul'),'native GLA'),
    (lambda d:d.update(post_run_dependencies_verified=False),'native GLA'),
    (lambda d:d.update(input_aig_sha256='0'*64),'source AIG'),
    (lambda d:d.update(proof_dependencies_sha256={}),'theorem closure'),
    (lambda d:d.update(abstracted_header=['aig','0','0','0','1','0']),'header changed'),
])
def test_modified_result_rejected(tmp_path,monkeypatch,mutation,match):
    if not GLA.exists():pytest.skip('External source-bound native GLA run unavailable')
    source=json.loads((GLA/'summary.json').read_text())
    original=Path.read_text
    changed=copy.deepcopy(source);mutation(changed)
    def read_text(path,*args,**kwargs):
        if path==GLA/'summary.json':return json.dumps(changed)
        return original(path,*args,**kwargs)
    monkeypatch.setattr(Path,'read_text',read_text)
    with pytest.raises(ValueError,match=match):driver.validate_native_gla(GLA)


@pytest.mark.parametrize('change',[False,True])
def test_postcheck_and_no_followup_solver(tmp_path,monkeypatch,change):
    proof=tmp_path/'proof';proof.write_text('valid')
    deps={str(proof):driver.digest(proof)}
    info={'execution':{'executable_sha256':driver.digest(Path('/usr/local/bin/abc'))},'prepared_directory':'prepared'}
    model={'core_json_sha256':'native','query_property_counts':{'assert':3,'assume':8,'cover':0}}
    monkeypatch.setattr(driver,'validate_native_gla',lambda path:(info,model,dict(deps)))
    monkeypatch.setattr(driver,'rederive_map',lambda *a,**k:{'exact':True})
    calls=[]
    def bmc(aig,directory,**kwargs):
        calls.append(kwargs)
        if change:proof.write_text('mutated')
        return {'status':'bounded_only_no_certificate','unbounded_certificate':False,'accepted_optimization':False,
            'reported_no_counterexample_frames':128}
    monkeypatch.setattr(driver,'run_bmc',bmc)
    result=driver.run_native_bmc(tmp_path/'gla',tmp_path/'result')
    assert len(calls)==1 and calls[0]['frames']==128 and calls[0]['timeout']==120
    assert result['status']==('error' if change else 'bounded_only_no_certificate')
    assert result['post_run_dependencies_verified'] is not change
    assert result['unbounded_certificate'] is False
