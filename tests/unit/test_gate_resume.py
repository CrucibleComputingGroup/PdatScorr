"""Fail-closed preservation guards before normal-GLA continuation."""
from pathlib import Path
import sys
import pytest

ROOT=Path(__file__).resolve().parents[2]
APP=ROOT/'experiments/bounded_dynamic/len5/application_screen'
sys.path[:0]=[str(ROOT),str(APP)]
from gate_resume import aig_parts,audit_map


def model(next_state=2,*,gate=True,constraints=False):
    raw=f'aig 2 1 1 1 0\n{next_state}\n4\n'.encode()+b'c'
    if gate:raw+=b'g'+(20).to_bytes(4,'big')+(1).to_bytes(4,'little')*5
    if constraints:raw+=b'c'+(4).to_bytes(4,'big')+(1).to_bytes(4,'big')
    return raw


def test_parser_keeps_exact_ordered_state_transition_and_gate_bytes(tmp_path):
    path=tmp_path/'map.aig';path.write_bytes(model())
    graph,extensions=aig_parts(path)
    assert graph==b'aig 2 1 1 1 0\n2\n4\n'
    assert extensions['g']==(1).to_bytes(4,'little')*5


def test_changed_latch_next_state_rejects_before_any_tool(tmp_path):
    mapped=tmp_path/'map.aig';mapped.write_bytes(model(0))
    original=tmp_path/'original.aig';original.write_bytes(model(2,gate=False))
    with pytest.raises(ValueError,match='exact original ordered GIA'):
        audit_map(mapped,original,original,tmp_path/'out',abc='/not/a/tool')


def test_missing_previous_map_rejects_before_any_tool(tmp_path):
    path=tmp_path/'no_map.aig';path.write_bytes(model(gate=False))
    with pytest.raises(ValueError,match='Missing previous gate classes'):
        audit_map(path,path,path,tmp_path/'out',abc='/not/a/tool')


def test_no_hidden_constraint_metadata(tmp_path):
    path=tmp_path/'constrained.aig';path.write_bytes(model(constraints=True))
    with pytest.raises(ValueError,match='Unfolded constraints'):aig_parts(path)


def test_corrupt_gate_class_indexing_rejects(tmp_path):
    path=tmp_path/'bad_map.aig';path.write_bytes(model().replace(b'g\0\0\0\x14',b'g\0\0\0\x10')[:-4])
    with pytest.raises(ValueError,match='Gate-class indexing'):aig_parts(path)
