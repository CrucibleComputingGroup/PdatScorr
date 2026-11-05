"""Primitive binding and state-rewrite guards for derived inactive-FU facts."""
import copy
import importlib.util
from pathlib import Path
import sys

import pytest

ROOT=Path(__file__).resolve().parents[2]
APP=ROOT/'experiments/bounded_dynamic/len5/application_screen'
sys.path[:0]=[str(ROOT),str(APP)]
spec=importlib.util.spec_from_file_location('inactive_fu_lemmas',APP/'inactive_fu_lemmas.py')
r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
from collect_inactive_fu import audit_query


def gate_module():
    cell={'type':'$and','parameters':{'A_WIDTH':1,'B_WIDTH':1,'Y_WIDTH':1},
        'connections':{'A':[10],'B':[11],'Y':[12]},
        'port_directions':{'A':'input','B':'input','Y':'output'}}
    return {'cells':{'insert':cell},'netnames':{n:{'bits':[b]} for n,b in
        [('rs.issue_valid_i',10),('rs.issue_ready_o',11),('rs.insert',12)]}}


def test_no_admission_discharge_requires_actual_zero_valid_and_exact_gate():
    module=gate_module();before=copy.deepcopy(module)
    assert r.insertion_binding(module,'rs.',10)['native_insert_bit']==12
    assert module==before
    with pytest.raises(ValueError,match='proved dispatch'):r.insertion_binding(module,'rs.',13)
    module['cells']['insert']['type']='$or'
    with pytest.raises(ValueError,match='exact proved-valid AND'):r.insertion_binding(module,'rs.',10)


def state_fixture():
    ff={'type':'$aldff','parameters':{'WIDTH':3,'CLK_POLARITY':1,'ALOAD_POLARITY':0},
        'attributes':{},'port_directions':{'CLK':'input','ALOAD':'input','AD':'input','D':'input','Q':'output'},
        'connections':{'CLK':[2],'ALOAD':[3],'AD':['0']*3,'D':[10,11,12],'Q':[20,21,22]}}
    cell={'type':'$and','parameters':{'A_WIDTH':1,'B_WIDTH':1,'Y_WIDTH':1},
        'port_directions':{'A':'input','B':'input','Y':'output'},'connections':{'A':[22],'B':[20],'Y':[30]}}
    design={'modules':{'datapath':{'cells':{'ff':ff,'use':cell},'ports':{
        'clk_i':{'direction':'input','bits':[2]},'rst_ni':{'direction':'input','bits':[3]},
        'observed':{'direction':'output','bits':[20,21,22]}},
        'netnames':{'all':{'bits':[20,21,22],'attributes':{}},'high_alias':{'bits':[22],'attributes':{}}}}}}
    return design,{'ireg_assigned_eu_ff':{'name':'ff','cell':copy.deepcopy(ff)},'ireg_high_bit':22}


def test_visible_state_substitution_slices_exact_ff_and_all_aliases_only():
    design,path=state_fixture();before=copy.deepcopy(design)
    result=r.substitute_visible_register_high(design,path);m=result['modules']['datapath']
    assert design==before
    assert m['cells']['ff']['connections']=={'CLK':[2],'ALOAD':[3],'AD':['0','0'],'D':[10,11],'Q':[20,21]}
    assert int(m['cells']['ff']['parameters']['WIDTH'],2)==2
    assert m['cells']['use']['connections']['A']==['0']
    assert m['ports']['observed']['bits']==[20,21,'0']
    assert m['netnames']['high_alias']['bits']==['0']
    assert m['ports']['clk_i']==before['modules']['datapath']['ports']['clk_i']


@pytest.mark.parametrize('mutation', ['input','init','changed_ff'])
def test_visible_state_rewrite_rejects_unproved_bindings(mutation):
    design,path=state_fixture();m=design['modules']['datapath']
    if mutation=='input':m['ports']['bad']={'direction':'input','bits':[22]}
    elif mutation=='init':m['netnames']['high_alias']['attributes']['init']='1'
    else:m['cells']['ff']['connections']['AD'][2]='1'
    with pytest.raises(ValueError):r.substitute_visible_register_high(design,path)


def test_external_initial_reset_must_bind_actual_native_clock_and_reset():
    design,path=state_fixture();m=design['modules']['datapath']
    r.validate_clock_reset(m,path)
    m['ports']['rst_ni']['bits']=[4]
    with pytest.raises(ValueError,match='external proof premises'):r.validate_clock_reset(m,path)


def test_changed_export_script_fails_before_tool_execution(tmp_path):
    old=tmp_path/'old';old.mkdir();(old/'export.ys').write_text('read_json malicious.json\n')
    with pytest.raises(ValueError,match='export commands changed'):
        r.replay_lowering(old,tmp_path/'new','yosys',sequential=True)


def test_independent_graph_audit_rejects_extra_logic_change():
    native,path=state_fixture();query=r.substitute_visible_register_high(native,path)
    summary={'row_reset_substitution':{'constant_substitutions':{}},
        'native_visible_register_high_substituted':22,'total_proved_reset_state_bits_substituted':1}
    assert audit_query(native,query,summary)['reset_bits']==1
    query['modules']['datapath']['cells']['use']['type']='$or'
    with pytest.raises(ValueError,match='beyond certified'):audit_query(native,query,summary)
