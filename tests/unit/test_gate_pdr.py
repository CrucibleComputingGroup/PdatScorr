"""Explicit PDR of GLA maps, including a spurious abstraction counterexample."""
from pathlib import Path
import sys

import pytest

ROOT=Path(__file__).resolve().parents[2]
APP=ROOT/'experiments/bounded_dynamic/len5/application_screen'
sys.path[:0]=[str(ROOT),str(APP)]
import gate_solver as gate
import gate_pdr

YOSYS='/home/allenjin/Projects/DAC_pscorr/tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys'


def source(negative=False):
    assumptions=' '.join(f'assume(!d[{i}]);' for i in range(1 if negative else 0,8))
    return ('module GateToy(input clk, input [7:0] d); reg q; reg seen=0;\n'
            'always @(posedge clk) begin q <= |d; seen <= 1; end\n'
            'always @* begin '+assumptions+' if(seen) assert(!q); end endmodule\n')


def derive(map_path,out):
    command=f'&read {gate.quote(map_path)}; &gla_derive; &write -s {gate.quote(out)}'
    result=gate.run_command(['/usr/local/bin/abc','-c',command],out.with_suffix('.log'),10)
    assert result['returncode']==0 and not result['timeout'] and out.exists()
    return out


@pytest.mark.parametrize('negative',[False,True])
def test_pdr_on_recorded_gla_maps_positive_and_negative(tmp_path,negative):
    if not Path(YOSYS).exists():pytest.skip('Pinned formal tools unavailable')
    aig,_=gate.prepare_toy(source(negative),tmp_path/'model',yosys=YOSYS)
    result=gate.run_gla(aig,tmp_path/'gla',timeout=3)
    assert result['status']==('counterexample_in_query_model' if negative else 'proved_safety_query_only')
    map_path=tmp_path/'gla'/('abstraction_map.aig' if negative else 'final_map.aig')
    abstract=derive(map_path,tmp_path/'abstract.aig')
    replay=gate_pdr.rederive_map(map_path,abstract,tmp_path/'replay')
    assert replay['abstracted_sha256']==replay['rederived_sha256']
    result=gate_pdr.run_pdr(abstract,tmp_path/'pdr',timeout=3)
    assert result['status']==('counterexample_in_abstraction_only' if negative else 'proved_overapproximation_safety')
    assert 'fold' not in result['execution']['argv'][-1]


def test_bounded_gla_can_have_spurious_pdr_counterexample(tmp_path):
    if not Path(YOSYS).exists():pytest.skip('Pinned formal tools unavailable')
    aig,_=gate.prepare_toy(source(False),tmp_path/'model',yosys=YOSYS)
    safe=gate.run_gla(aig,tmp_path/'unbounded',timeout=3)
    assert safe['status']=='proved_safety_query_only'
    map_path=tmp_path/'bounded_map.aig'
    command=(f'read_aiger {gate.quote(aig)}; fold; orpos; &get; &gla -F 1 -T 2; '
             f'&write -s {gate.quote(map_path)}')
    execution=gate.run_command(['/usr/local/bin/abc','-c',command],tmp_path/'bounded.log',7)
    assert execution['returncode']==0 and 'proved abstraction' not in (tmp_path/'bounded.log').read_text()
    abstract=derive(map_path,tmp_path/'abstract.aig')
    result=gate_pdr.run_pdr(abstract,tmp_path/'pdr',timeout=3)
    assert result['status']=='counterexample_in_abstraction_only'
    assert result['counterexample_validation']['returncode']==0
    assert result['accepted_optimization'] is False


def test_unfolded_constraints_are_rejected_before_solver(tmp_path):
    path=tmp_path/'bad.aig';path.write_bytes(b'aig 2 1 0 1 1 0 1\n')
    with pytest.raises(ValueError,match='no remaining constraints'):
        gate_pdr.run_pdr(path,tmp_path/'pdr',timeout=1)
