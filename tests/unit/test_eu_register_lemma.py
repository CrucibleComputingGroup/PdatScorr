"""Tiny actual-primitive tests for reset-masked selector history."""
import copy
import importlib.util
from pathlib import Path
import shutil
import sys

import pytest

ROOT=Path(__file__).resolve().parents[2]
APP=ROOT/'experiments/bounded_dynamic/len5/application_screen'
sys.path[:0]=[str(ROOT),str(APP)]
spec=importlib.util.spec_from_file_location('eu_register_lemma',APP/'eu_register_lemma.py')
r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)


def fixture_path():
    def mux(a,b,s,y):return {'type':'$mux','hide_name':0,'attributes':{},'parameters':{'WIDTH':1},
        'port_directions':{'A':'input','B':'input','S':'input','Y':'output'},'connections':{'A':[a],'B':[b],'S':[s],'Y':[y]}}
    ff={'type':'$aldff','hide_name':0,'attributes':{},'parameters':{'WIDTH':3,'CLK_POLARITY':1,'ALOAD_POLARITY':0},
        'port_directions':{'CLK':'input','ALOAD':'input','AD':'input','D':'input','Q':'output'},
        'connections':{'CLK':[2],'ALOAD':[3],'AD':['0']*3,'D':[21,22,23],'Q':[31,32,33]}}
    return {'native_high_bit_data_mux_slices':{'hold':mux(33,12,4,20),'inner':mux(20,'x',5,24),'outer':mux(24,'0',5,23)},
        'ireg_assigned_eu_ff':{'name':'native_ff','cell':ff},'ireg_high_bit':33,
        'decoder_assigned_eu_bits':[10,11,12],'arbitrary_control_cut_candidates':[4,5]}


def test_projection_retains_shared_selector_and_native_visible_q():
    source=fixture_path();before=copy.deepcopy(source);design=r.register_projection(source)
    m=design['modules']['NativeEURegister'];assert source==before
    assert m['ports']['visible_high']['bits']==[33]
    assert m['cells']['native_ff']['connections']['D']==[23] and m['cells']['native_ff']['connections']['Q']==[33]
    assert m['cells']['inner']['connections']['B']==['x']
    assert m['cells']['inner']['connections']['S']==m['cells']['outer']['connections']['S']==[5]


def test_shared_flush_masks_x_but_independent_flush_must_fail(tmp_path):
    yosys=shutil.which('yosys')
    if not yosys or not shutil.which('yosys-smtbmc') or not shutil.which('z3'):pytest.skip('Yosys/Z3 required')
    source=fixture_path();good=r.run_proof(r.register_projection(source),tmp_path/'good',yosys=yosys)
    assert good['status']=='proved_unbounded'
    bad=copy.deepcopy(source);bad['native_high_bit_data_mux_slices']['inner']['connections']['S']=[6]
    bad['arbitrary_control_cut_candidates'].append(6)
    result=r.run_proof(r.register_projection(bad),tmp_path/'bad',yosys=yosys)
    assert result['status']=='counterexample_found'
    relaxed=r.run_proof(r.register_projection(source),tmp_path/'relaxed',yosys=yosys,derived_premise=False)
    assert relaxed['status']=='counterexample_found'


def test_visible_state_cannot_be_cut_as_arbitrary_input():
    source=fixture_path();source['arbitrary_control_cut_candidates'].append(33)
    with pytest.raises(ValueError,match='cut/driver collision'):r.register_projection(source)
