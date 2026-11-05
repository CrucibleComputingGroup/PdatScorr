"""Real bounded-engine smoke controls and fail-closed status checks."""
from pathlib import Path
import sys
import pytest

ROOT=Path(__file__).resolve().parents[2]
APP=ROOT/'experiments/bounded_dynamic/len5/application_screen'
sys.path[:0]=[str(ROOT),str(APP)]
import gate_bmc
import gate_solver

YOSYS='/home/allenjin/Projects/DAC_pscorr/tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys'


@pytest.mark.parametrize('negative',[False,True])
def test_real_bounded_positive_and_negative(tmp_path,negative):
    if not Path(YOSYS).exists():pytest.skip('Pinned tools unavailable')
    premise='' if negative else 'assume(!d);'
    source='module GateToy(input clk,input d); reg q; reg seen=0; always @(posedge clk) begin q<=d;seen<=1;end always @* begin '+premise+' if(seen) assert(!q);end endmodule'
    raw,_=gate_solver.prepare_toy(source,tmp_path/'model',yosys=YOSYS)
    aig=tmp_path/'folded.aig'
    execution=gate_solver.run_command(['/usr/local/bin/abc','-c',f'read_aiger {gate_solver.quote(raw)}; fold; orpos; write_aiger {gate_solver.quote(aig)}'],tmp_path/'fold.log',10)
    assert execution['returncode']==0 and not execution['timeout']
    result=gate_bmc.run_bmc(aig,tmp_path/'bmc',frames=8,timeout=3)
    assert result['status']==('counterexample_in_abstraction_only' if negative else 'bounded_only_no_certificate')
    assert result['unbounded_certificate'] is False and result['accepted_optimization'] is False
    assert 'fold' not in result['execution']['argv'][-1].split(';',1)[1]
    if negative:assert result['counterexample_validation']['returncode']==0


@pytest.mark.parametrize('execution,log,status',[
    ({'returncode':0,'timeout':False},'No output asserted in 7 frames.','snl_UNK'),
    ({'returncode':0,'timeout':True},'No output asserted in 8 frames.','snl_UNK'),
    ({'returncode':1,'timeout':False},'No output asserted in 8 frames.','snl_UNK'),
    ({'returncode':0,'timeout':False},'No output asserted in 8 frames.\nTime limit reached','snl_UNK'),
    ({'returncode':0,'timeout':False},'No output asserted in 8 frames.','snl_SAT'),
    ({'returncode':0,'timeout':False},'Output 0 of miter x was asserted in frame 1.\nNo output asserted in 8 frames.','snl_SAT'),
])
def test_incomplete_or_contradictory_status_never_certifies(execution,log,status):
    assert gate_bmc.verdict(execution,log,status,8)=='unknown_no_certificate'
