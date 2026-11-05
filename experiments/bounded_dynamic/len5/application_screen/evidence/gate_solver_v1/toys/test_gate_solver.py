"""Installed ABC GLA regressions: constraints, uninitialized FFs, and verdicts."""
import importlib.util
from pathlib import Path
import shutil
import sys

import pytest

ROOT=Path(__file__).resolve().parents[2]
APP=ROOT/'experiments/bounded_dynamic/len5/application_screen'
sys.path[:0]=[str(ROOT),str(APP)]
import gate_solver as gate

YOSYS='/home/allenjin/Projects/DAC_pscorr/tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys'


def case_source(kind):
    if kind=='arbitrary_initial_invariant':
        return '''module GateToy(input clk, input d);
reg [1:0] q; reg previous; reg seen=0;
always @(posedge clk) begin q <= q+2; previous <= q[0]; seen <= 1; end
always @* if(seen) assert(q[0] == previous);
endmodule
'''
    if kind=='arbitrary_initial_negative':
        return '''module GateToy(input clk, input d);
reg q; always @(posedge clk) q <= 0;
always @* begin assume(!d); assert(!q); end
endmodule
'''
    assumptions=''.join(f'assume(!d[{i}]); ' for i in range(8) if kind!='missing_one_assumption' or i!=0)
    return '''module GateToy(input clk, input [7:0] d);
reg q; reg seen=0;
always @(posedge clk) begin q <= |d; seen <= 1; end
always @* begin '''+assumptions+''' if(seen) assert(!q); end
endmodule
'''


@pytest.mark.parametrize('kind,expected',[
    ('arbitrary_initial_invariant','proved_safety_query_only'),
    ('eight_assumptions','proved_safety_query_only'),
    ('missing_one_assumption','counterexample_in_query_model'),
    ('arbitrary_initial_negative','counterexample_in_query_model'),
])
def test_real_gla_preserves_constraints_and_unknown_initial_state(tmp_path,kind,expected):
    if not Path(YOSYS).exists() or not Path('/usr/local/bin/abc').exists(): pytest.skip('Pinned formal tools unavailable')
    aig,prepared=gate.prepare_toy(case_source(kind),tmp_path/'model',yosys=YOSYS)
    record=gate.run_gla(aig,tmp_path/'gla',timeout=3)
    assert record['status']==expected, (record,(tmp_path/'gla/gla.log').read_text())
    assert record['accepted_optimization'] is False
    assert int(record['folded_header'][4])==1
    if expected=='counterexample_in_query_model':
        assert (tmp_path/'gla/counterexample.aiw').exists()
        assert record['counterexample_validation']['returncode']==0
    if kind=='eight_assumptions':assert int(prepared['aig_header'][7])==8


@pytest.mark.parametrize('log,status',[
    ('GLA finished 64 frames and produced a 62-stable abstraction.','snl_UNK 63 unknown'),
    ('GLA reached timeout 120 sec in frame 31 with a 3-stable abstraction.','snl_UNK 30 unknown'),
    ('No output asserted in 100 frames.','snl_UNSAT 99 unknown'),
    ('Proved abstraction 1.','snl_UNSAT 5 unknown'),
    ('GLA completed 8 frames and proved abstraction derived in frame 3','snl_UNK 7 unknown'),
])
def test_stability_bounded_checks_and_incomplete_proof_messages_are_unknown(log,status):
    assert gate.verdict({'timeout':False,'returncode':0},log,status)=='unknown'


def test_even_explicit_result_rejected_after_timeout_or_engine_error():
    log='GLA completed 8 frames and proved abstraction derived in frame 3'
    assert gate.verdict({'timeout':True,'returncode':0},log,'snl_UNSAT -1 unknown')=='unknown'
    assert gate.verdict({'timeout':False,'returncode':0},log+'\nError: corrupted map','snl_UNSAT -1 unknown')=='error'
