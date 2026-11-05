"""Fail-closed native-cube orchestration checks using tiny real RTL/SAT."""
import copy
import importlib.util
from pathlib import Path
import sys

import pytest

ROOT = Path(__file__).resolve().parents[2]
APP = ROOT/'experiments/bounded_dynamic/len5/application_screen'
sys.path.insert(0, str(APP))
import reset_cube_fixedpoint as fixed

spec = importlib.util.spec_from_file_location('reset_cube_test_rtl', Path(__file__).with_name('test_reset_cube.py'))
rtl = importlib.util.module_from_spec(spec)
spec.loader.exec_module(rtl)


def test_certified_mutual_cube_emits_only_exact_constant_patch(tmp_path):
    design = rtl.compile_rtl('''module Tiny(input clk_i,rst_ni,output reg [3:0] a,b);
      always @(posedge clk_i or negedge rst_ni) if(!rst_ni) begin a<=9;b<=9;end
        else begin a<=b;b<=a;end endmodule''', tmp_path/'rtl')
    result = fixed.run(design, 'Tiny', tmp_path/'run', yosys=rtl.YOSYS, seconds=15, proof_seconds=10)
    assert result['status'] == 'reset_cube_certified_query_patch_only'
    assert result['certified_words'] == 2 and result['certified_bits'] == 8
    assert result['graph_audit']['formal_cells_added'] == 0
    assert all(x['status'] == 'proved_combinationally' for x in result['final_proofs'].values())
    patch = fixed.read(tmp_path/'run/query_only_patch.json')
    assert patch['modules']['Tiny']['ports']['a']['bits'] == ['1','0','0','1']


def test_iteration_cap_never_certifies_partial_cube(tmp_path):
    design = rtl.compile_rtl('''module Tiny(input clk_i,rst_ni,d,output reg a,b);
      always @(posedge clk_i or negedge rst_ni) if(!rst_ni) begin a<=0;b<=0;end
        else begin a<=d;b<=a;end endmodule''', tmp_path/'rtl')
    result = fixed.run(design, 'Tiny', tmp_path/'run', yosys=rtl.YOSYS, max_rounds=1, seconds=15)
    assert result['status'] == 'incomplete_iteration_cap_no_certificate'
    assert result['certified_bits'] == 0 and not (tmp_path/'run/query_only_patch.json').exists()


def test_false_structural_fixed_point_still_needs_real_sat(tmp_path, monkeypatch):
    design = rtl.compile_rtl('''module Tiny(input clk_i,rst_ni,d,output reg q);
      always @(posedge clk_i or negedge rst_ni) if(!rst_ni) q<=0;else q<=d;
      endmodule''', tmp_path/'rtl')
    actual = fixed.prepare
    def false_structural(*args, **kwargs):
        result = actual(*args, **kwargs)
        if kwargs.get('solve') is False:
            result['initial_cofactor_output_constants'] = {name:'0' for name in result['initial_cofactor_output_constants']}
        return result
    monkeypatch.setattr(fixed, 'prepare', false_structural)
    result = fixed.run(design, 'Tiny', tmp_path/'run', yosys=rtl.YOSYS, seconds=15, proof_seconds=10)
    assert result['native_fixed_point'] is True
    assert result['status'] == 'final_proof_failed_no_certificate'
    assert result['final_proofs']['induction']['status'] == 'counterexample'
    assert result['certified_bits'] == 0 and not (tmp_path/'run/query_only_patch.json').exists()
