"""Real RTL/SAT checks for standalone simultaneous reset-word induction."""
import json
from pathlib import Path
import sys

import pytest

ROOT = Path(__file__).resolve().parents[2]
APP = ROOT/'experiments/bounded_dynamic/len5/application_screen'
sys.path.insert(0, str(APP))
import reset_cube as cube

YOSYS = Path('/home/allenjin/Projects/DAC_pscorr/tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys')


def compile_rtl(text, directory, *, enables=False):
    if not YOSYS.exists():
        pytest.skip('Qualified local Yosys unavailable')
    directory.mkdir()
    source = directory/'source.sv'
    source.write_text(text)
    script = f'read_verilog -sv {cube.quoted(source)}\nhierarchy -top Tiny\nproc -noopt\nsetundef -anyseq\nflatten\nopt_expr -keepdc\nopt_clean\n'
    if enables:
        script += 'opt_dff\n'
    script += f'write_json {cube.quoted(directory/"source.json")}\n'
    execution = cube.execute(script, directory/'compile', YOSYS, 15)
    assert execution['returncode'] == 0 and not execution['timeout']
    return cube.read(directory/'source.json')


def run(text, tmp_path, *, enables=False, prepare_only=False):
    design = compile_rtl(text, tmp_path/'rtl', enables=enables)
    result = cube.discover(design, 'Tiny', tmp_path/'proof', yosys=YOSYS, timeout=15, prepare_only=prepare_only)
    return design, result


def test_mutually_inductive_words_and_nonzero_reset(tmp_path):
    _, result = run('''module Tiny(input clk_i,rst_ni, output reg [2:0] a,b);
      always @(posedge clk_i or negedge rst_ni) if(!rst_ni) begin a<=3'b101;b<=3'b101;end
        else begin a<=b;b<=a;end endmodule''', tmp_path)
    assert result['status'] == 'reset_cube_proved' and result['selected_bits'] == 6
    assert len(result['selected_words']) == 2
    assert all(row['reset_value'] == list('101') for row in result['selected_words'])
    assert result['base']['status'] == result['rounds'][-1]['proof']['status'] == 'proved_combinationally'


def test_descending_cube_rechecks_dependents_after_seed_is_refuted(tmp_path):
    _, result = run('''module Tiny(input clk_i,rst_ni,d, output reg a,b);
      always @(posedge clk_i or negedge rst_ni) if(!rst_ni) begin a<=0;b<=0;end
        else begin a<=d;b<=a;end endmodule''', tmp_path)
    assert result['status'] == 'empty_cube_no_simplification'
    assert [r['candidate_words'] for r in result['rounds']] == [2, 1]
    assert all(r['proof']['status'] == 'counterexample' for r in result['rounds'])


def test_enabled_mutual_nonzero_words_preserve_reset_priority(tmp_path):
    design, result = run('''module Tiny(input clk_i,rst_ni,en, output reg [1:0] a,b);
      always @(posedge clk_i or negedge rst_ni) if(!rst_ni) a<=2'b10; else if(en) a<=b;
      always @(posedge clk_i or negedge rst_ni) if(!rst_ni) b<=2'b10; else if(!en) b<=a;
      endmodule''', tmp_path, enables=True)
    assert any(c['type'] == '$adffe' for c in design['modules']['Tiny']['cells'].values())
    assert result['status'] == 'reset_cube_proved' and result['selected_bits'] == 4


@pytest.mark.parametrize('condition', ['en', '!en'])
def test_enabled_new_data_cannot_be_assumed_idle(tmp_path, condition):
    _, result = run(f'''module Tiny(input clk_i,rst_ni,en,d, output reg q);
      always @(posedge clk_i or negedge rst_ni) if(!rst_ni) q<=0; else if({condition}) q<=d;
      endmodule''', tmp_path, enables=True)
    assert result['status'] == 'empty_cube_no_simplification'


def test_unmasked_undefined_update_refutes_zero(tmp_path):
    _, result = run('''module Tiny(input clk_i,rst_ni,en, output reg q);
      always @(posedge clk_i or negedge rst_ni) if(!rst_ni) q<=0; else q<=en?1'bx:1'b0;
      endmodule''', tmp_path)
    assert result['status'] == 'empty_cube_no_simplification'
    assert result['rounds'][0]['proof']['status'] == 'counterexample'


def test_shared_flush_correlation_masks_undefined_branch(tmp_path):
    _, result = run('''module Tiny(input clk_i,rst_ni,flush, output reg q);
      wire x_or_hold=flush?1'bx:q;
      always @(posedge clk_i or negedge rst_ni) if(!rst_ni) q<=0; else q<=flush?1'b0:x_or_hold;
      endmodule''', tmp_path)
    assert result['status'] == 'reset_cube_proved' and result['selected_bits'] == 1


def test_wrong_clock_reset_and_unknown_reset_are_not_candidates(tmp_path):
    design = compile_rtl('''module Tiny(input clk_i,other_clk,rst_ni,other_rst,d, output reg a,b,c,e,f,g);
      always @(posedge clk_i or negedge rst_ni) if(!rst_ni) a<=0;else a<=a;
      always @(negedge clk_i or negedge rst_ni) if(!rst_ni) b<=0;else b<=b;
      always @(posedge other_clk or negedge rst_ni) if(!rst_ni) c<=0;else c<=c;
      always @(posedge clk_i or negedge other_rst) if(!other_rst) e<=0;else e<=e;
      always @(posedge clk_i or posedge rst_ni) if(rst_ni) f<=0;else f<=f;
      always @(posedge clk_i or negedge rst_ni) if(!rst_ni) g<=1'bx;else g<=g;
      endmodule''', tmp_path/'rtl')
    rows, audit = cube.eligibility(design, 'Tiny')
    assert len(rows) == 1 and len(audit['rejected_state_cells']) == 5
    assert rows[0]['q'] == design['modules']['Tiny']['netnames']['a']['bits']


def test_nonresettable_state_is_arbitrary_not_guessed_zero(tmp_path):
    _, result = run('''module Tiny(input clk_i,rst_ni,d, output reg a,q);
      always @(posedge clk_i) a<=d;
      always @(posedge clk_i or negedge rst_ni) if(!rst_ni) q<=0;else q<=a;
      endmodule''', tmp_path)
    assert result['eligibility']['eligible_words'] == 1
    assert result['status'] == 'empty_cube_no_simplification'


def test_prepare_only_never_certifies_even_a_true_cube(tmp_path):
    _, result = run('''module Tiny(input clk_i,rst_ni, output reg q);
      always @(posedge clk_i or negedge rst_ni) if(!rst_ni) q<=0;else q<=q;
      endmodule''', tmp_path, prepare_only=True)
    assert result['status'] == 'prepared_only_no_invariant_certificate'
    assert result['selected_words'] == [] and result['selected_bits'] == 0


def test_native_async_load_primitive_with_constant_bound_reset_data(tmp_path):
    design, result = run('''module AsyncLoad(input clk_i,rst_ni, input [1:0] initial_value,d,
        output reg [1:0] q);
      always @(posedge clk_i or negedge rst_ni) if(!rst_ni) q<=initial_value;else q<=d;
      endmodule
      module Tiny(input clk_i,rst_ni, output [1:0] a,b);
      AsyncLoad first(clk_i,rst_ni,2'b01,b,a);
      AsyncLoad second(clk_i,rst_ni,2'b01,a,b);
      endmodule''', tmp_path)
    assert any(c['type'] == '$aldff' for c in design['modules']['Tiny']['cells'].values())
    assert result['status'] == 'reset_cube_proved' and result['selected_bits'] == 4


def test_one_variable_bit_discards_entire_64bit_word(tmp_path):
    _, result = run('''module Tiny(input clk_i,rst_ni,d, output reg [63:0] q);
      always @(posedge clk_i or negedge rst_ni) if(!rst_ni) q<=0;else q<={q[63:1],d};
      endmodule''', tmp_path)
    assert result['eligibility']['eligible_words'] == 1 and result['eligibility']['eligible_bits'] == 64
    assert result['status'] == 'empty_cube_no_simplification' and len(result['rounds']) == 1


def test_other_memory_contents_are_arbitrary(tmp_path):
    _, result = run('''module Tiny(input clk_i,rst_ni,we,addr,d, output reg q);
      reg mem[0:1];
      always @(posedge clk_i) if(we) mem[addr]<=d;
      always @(posedge clk_i or negedge rst_ni) if(!rst_ni) q<=0;else q<=mem[addr];
      endmodule''', tmp_path)
    assert result['eligibility']['native_memory_arrays'] == 1
    assert result['status'] == 'empty_cube_no_simplification'
