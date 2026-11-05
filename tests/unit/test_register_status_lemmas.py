"""Native register-status binding/rewrite and real negative-witness checks."""
import copy
from pathlib import Path
import sys
import pytest

ROOT=Path(__file__).resolve().parents[2]
APP=ROOT/'experiments/bounded_dynamic/len5/application_screen'
sys.path[:0]=[str(ROOT),str(APP)]
import register_status_lemmas as helper
import collect_register_status as audit

BUILD=Path('/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build')
RUN=BUILD/'register_status_lemmas_v2'


@pytest.fixture(scope='module')
def native():
    if not RUN.exists():pytest.skip('Source-bound local proof artifacts unavailable')
    return helper.read(BUILD/'isa_baseline_prepare_v1/whole_core.json')


def test_whole_native_component_and_exact_index_bindings(native):
    component,record=helper.native_component(native,[0,5,8,9,10,11,18])
    assert len(record['native_component_cells'])==506 and record['native_state_bits']==341
    assert record['reset_bits']==275 and len(record['unused_entries'])==25
    ports=component['modules']['NativeRegisterStatus']['ports']
    assert ports['issue_rd_idx_i']['bits']==[461,462,463,464,465]
    assert ports['comm_rd_idx_i']['bits']==[466,467,468,469,470]


@pytest.mark.parametrize('mutation',[
    lambda c:c['connections']['AD'].__setitem__(0,'x'),
    lambda c:c['connections'].__setitem__('ALOAD',[2]),
    lambda c:c['parameters'].__setitem__('CLK_POLARITY','0'),
])
def test_wrong_native_reset_or_clock_rejected(native,mutation):
    changed=copy.deepcopy(native)
    mutation(changed['modules']['datapath']['cells']['$driver$u_backend.u_int_regstat.busy_rob_idx[1]'])
    with pytest.raises(ValueError):helper.native_component(changed,[0,5,8,9,10,11,18])


def test_harness_only_derived_indexes_and_reset(native):
    component,record=helper.native_component(native,[0,5,8,9,10,11,18])
    positive=helper.harness(component,record,[0,5,8,9,10,11,18])
    assert positive.count('assume(')==3 and positive.count('assert(')==50
    assert 'assume(!(insert' not in positive and 'if (rst_ni) assume' not in positive
    for kind in ('issue','commit'):
        negative=helper.harness(component,record,[0,5,8,9,10,11,18],relax=kind)
        assert negative.count('assume(')==2 and negative.count('assert(')==50


def test_mutator_rechecks_selected_reset_binding(native):
    _,record=helper.native_component(native,[0,5,8,9,10,11,18])
    stale=copy.deepcopy(native)
    stale['modules']['datapath']['cells'][record['unused_entries'][0]['fields'][0]['native_cell']]['connections']['AD'][0]='1'
    with pytest.raises(ValueError,match='Reset-state source binding'):helper.reset_substitution(stale,record)


@pytest.mark.parametrize('kind,new_count',[('issue',1),('commit',63)])
def test_actual_negative_trace_has_enabled_nonreset_update(native,kind,new_count):
    record=audit.negative_witness(RUN/f'negative_{kind}'/'counterexample.vcd',kind,[0,5,8,9,10,11,18])
    assert record['failure_step']==2 and record['update_step']==1
    assert record['old_count']==0 and record['new_count']==new_count
    assert record['register'] not in [0,5,8,9,10,11,18]


def test_full_record_and_independent_graph_audit(native):
    result,record=audit.audit_run(RUN)
    assert record['proved_reset_bits']==275 and record['removed_ff_cells']==50
    assert record['rd_projection_cells_preserved']==381
    assert result['accepted_optimization'] is False
