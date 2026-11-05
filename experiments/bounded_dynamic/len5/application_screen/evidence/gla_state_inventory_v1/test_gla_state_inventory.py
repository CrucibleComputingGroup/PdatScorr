"""Exact provenance checks for a solver-free retained-state inventory."""
from pathlib import Path
import copy
import sys
import pytest

ROOT=Path(__file__).resolve().parents[2]
APP=ROOT/'experiments/bounded_dynamic/len5/application_screen'
sys.path[:0]=[str(ROOT),str(APP)]
from gla_state_inventory import read_aig,transition_binding,source_owners


def aig(latches, *, inputs=1, nodes=()):
    return {'header':[inputs+len(latches)+len(nodes),inputs,len(latches),0,len(nodes),0,0,0,0],
            'latches':latches,'nodes':nodes,'observations':[]}


def test_identical_order_and_appended_history_are_structurally_bound():
    original=aig([(2,0),(4,0)])
    folded=aig([(2,0),(4,0),(6,0)])
    assert transition_binding(original,folded)['established']


def test_reordered_or_mutated_next_state_is_rejected():
    original=aig([(2,0),(4,0)])
    for changed in [[(4,0),(2,0),(6,0)],[(0,0),(4,0),(6,0)]]:
        result=transition_binding(original,aig(changed))
        assert not result['established'] and result['mismatched_indices']


def test_changed_initial_value_rejects_despite_equal_transitions():
    result=transition_binding(aig([(2,0)]),aig([(2,1),(4,0)]))
    assert not result['established'] and not result['all_existing_initial_values_match']


def test_literal_polarity_and_pi_identity_are_not_erased():
    assert not transition_binding(aig([(2,)]),aig([(3,),(4,)]))['established']
    with pytest.raises(ValueError,match='same inputs'):
        transition_binding(aig([(2,)]),aig([(2,),(4,)],inputs=2))


def test_equivalent_elementary_and_rewrite_is_allowed():
    original=aig([(6,)],nodes=[(2,2)])
    folded=aig([(2,),(4,)])
    assert transition_binding(original,folded)['established']


def test_binary_parser_preserves_unknown_initial_state_literal(tmp_path):
    path=tmp_path/'source.aig';path.write_bytes(b'aig 2 1 1 0 0\n2 4\nc')
    assert read_aig(path)['latches']==[(2,4)]


def model():
    return {'cells':{'native':{'type':'$dff','port_directions':{'Q':'output','D':'input'},
        'connections':{'Q':[3,4],'D':[2,3]}},'mask':{'type':'$mux',
        'port_directions':{'Y':'output','A':'input','B':'input','S':'input'},
        'connections':{'Y':[6],'A':['0'],'B':[3],'S':[5]}}},
        'netnames':{'packed':{'bits':[3,4],'offset':7},'visible':{'bits':[6]}}}


def test_direct_state_and_visible_reset_mask_keep_distinct_routes(tmp_path):
    path=tmp_path/'map';path.write_text('latch 0 8 packed\nlatch 1 0 visible\n')
    owners,unresolved=source_owners(model(),path)
    assert list(owners[0])==[('native',1)]
    assert list(owners[1])==[('native',0)]
    assert not list(owners[0].values())[0]['route']
    assert list(owners[1].values())[0]['route'][0]['kind']=='reset_constant_mux_owner_lineage'
    assert not unresolved


def test_arbitrary_two_state_mux_is_not_given_single_owner(tmp_path):
    path=tmp_path/'map';path.write_text('latch 0 0 visible\n')
    m=model();m['cells']['mask']['connections']['A']=[4]
    owners,unresolved=source_owners(m,path)
    assert not owners and unresolved[0][0]['type']=='$mux'


def test_ambiguous_driver_missing_alias_and_offset_reject(tmp_path):
    path=tmp_path/'map';path.write_text('latch 0 8 packed\n')
    m=model();m['cells']['duplicate']=copy.deepcopy(m['cells']['native'])
    with pytest.raises(ValueError,match='Ambiguous'):source_owners(m,path)
    path.write_text('latch 0 0 absent\n')
    with pytest.raises(ValueError,match='alias missing'):source_owners(model(),path)
    path.write_text('latch 0 6 packed\n')
    with pytest.raises(ValueError,match='offset out of range'):source_owners(model(),path)
