"""Actual generic scalar-ODC discovery, without processor-specific candidates."""
import copy
import json
from pathlib import Path
import shutil
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from odc.state_candidates import scalar_constant_candidates, replace_scalar_constant
from odc.temporal import digest, export_design, prove_pair

YOSYS = shutil.which('yosys')
SMTBMC = shutil.which('yosys-smtbmc')
ABC = shutil.which('abc') or shutil.which('yosys-abc')
integration = pytest.mark.skipif(not all((YOSYS, SMTBMC, ABC)), reason='Yosys/ABC formal tools required')


def eq_cell(y, a=2, b=3):
    return {'type':'$eq', 'parameters':{'A_WIDTH':'1','B_WIDTH':'1','Y_WIDTH':'1',
                                      'A_SIGNED':'0','B_SIGNED':'0'},
            'attributes':{}, 'connections':{'A':[a],'B':[b],'Y':[y]},
            'port_directions':{'A':'input','B':'input','Y':'output'}}


def structural_fixture():
    cells = {'eligible':eq_cell(8), 'input_alias':eq_cell(2),
             'q_alias':eq_cell(9), 'multi_a':eq_cell(10), 'multi_b':eq_cell(10),
             'state':{'type':'$dff','parameters':{'WIDTH':'1','CLK_POLARITY':'1'},
                      'attributes':{}, 'connections':{'CLK':[4],'D':[8],'Q':[9]},
                      'port_directions':{'CLK':'input','D':'input','Q':'output'}}}
    return {'modules':{'Toy':{'ports':{'a':{'direction':'input','bits':[2]},
                                      'b':{'direction':'input','bits':[3]},
                                      'clk':{'direction':'input','bits':[4]},
                                      'q':{'direction':'output','bits':[9]}},
                              'netnames':{'eligible_wire':{'bits':[8],'attributes':{}},
                                          'state_wire':{'bits':[9],'attributes':{}}},
                              'cells':cells}}}


def test_enumeration_rejects_input_state_and_multiple_drivers():
    design = structural_fixture()
    candidates = scalar_constant_candidates(design, 'Toy')
    assert [(c['cell'],c['constant']) for c in candidates] == [('eligible',0),('eligible',1)]
    assert scalar_constant_candidates(design,'Toy','does_not_match') == []


def test_logic_not_scalar_nodes_have_both_untrusted_constants():
    design = structural_fixture()
    design['modules']['Toy']['cells']['not_node'] = {
        'type':'$logic_not','parameters':{'A_WIDTH':'10','A_SIGNED':'0','Y_WIDTH':'1'},
        'attributes':{},'connections':{'A':[2,3],'Y':[12]},
        'port_directions':{'A':'input','Y':'output'}}
    candidates = scalar_constant_candidates(design,'Toy','not_node')
    assert [c['constant'] for c in candidates] == [0,1]
    changed = replace_scalar_constant(design,'Toy',candidates[1])
    assert changed['modules']['Toy']['cells']['not_node']['connections'] == {'A':['1'],'Y':[12]}


@pytest.mark.parametrize('value', [0,1])
def test_replacement_preserves_ports_names_all_other_drivers_and_input(value):
    design = structural_fixture()
    before = copy.deepcopy(design)
    candidate = scalar_constant_candidates(design,'Toy')[value]
    changed = replace_scalar_constant(design,'Toy',candidate)
    assert design == before
    a,b = design['modules']['Toy'],changed['modules']['Toy']
    assert a['ports'] == b['ports'] and a['netnames'] == b['netnames']
    for name in a['cells']:
        if name != 'eligible':
            assert a['cells'][name] == b['cells'][name]
    assert b['cells']['eligible']['type'] == '$pos'
    assert b['cells']['eligible']['connections'] == {'A':[str(value)],'Y':[8]}


@pytest.mark.parametrize('cell,bit', [('input_alias',2),('q_alias',9),('multi_a',10)])
def test_mutator_independently_rejects_forbidden_driver(cell,bit):
    with pytest.raises(ValueError, match='eligible unique scalar driver'):
        replace_scalar_constant(structural_fixture(),'Toy',
                                {'cell':cell,'constant':0,'output_bit':bit,'original_type':'$eq'})


def elaborate(folder, text):
    source, design = folder/'source.sv',folder/'source.json'
    source.write_text(text)
    result = subprocess.run([YOSYS,'-Q','-T','-p',
        f'read_verilog -sv "{source}"; hierarchy -top Toy; proc; opt; write_json "{design}"'],
        text=True,capture_output=True,timeout=30)
    assert result.returncode == 0,result.stdout+result.stderr
    return design


def analyze(design, harness, output, scope='.*', maximum=8):
    before = {p:digest(p) for p in (design,harness)}
    command = [sys.executable,str(ROOT/'scripts/analyze_state_odc.py'),str(design),
               '--top','Toy','--candidate-top','ToyCandidate','--harness',str(harness),
               '--output',str(output),'--scope',scope,'--max-probes',str(maximum),
               '--yosys',YOSYS,'--smtbmc',SMTBMC,'--abc',ABC,'--engine','pdr','--timeout','20']
    result = subprocess.run(command,text=True,capture_output=True,timeout=60)
    assert result.returncode == 0,result.stdout+result.stderr
    report = json.loads((output/'report.json').read_text())
    assert report['status'] == 'proved' and report['combined_proof']['proven']
    assert not report['assert_state_correspondence']
    assert all(digest(p)==value for p,value in before.items())
    assert report['combined_proof']['candidate_sha256'] == digest(output/'optimized.v')
    return report


@integration
def test_nonconstant_hidden_state_control_accepts_functional_odc(tmp_path):
    design = elaborate(tmp_path,'''module Toy(input clk,d,input [1:0] a,b,output reg q);
      (* keep *) reg hidden;
      (* keep *) wire hidden_eq = a == b;
      always @(posedge clk) begin hidden <= hidden_eq; q <= d; end
    endmodule''')
    harness = tmp_path/'harness.sv'
    harness.write_text('''module TemporalMiter(input clk);
      (* anyseq *) reg d;
      (* anyseq *) reg [1:0] a,b;
      wire x,y;
      Toy reference(clk,d,a,b,x); ToyCandidate candidate(clk,d,a,b,y);
      always @* assert(x == y);
    endmodule''')
    report = analyze(design,harness,tmp_path/'analysis',scope='hidden_eq')
    assert len(report['accepted']) == 1 and report['accepted'][0]['constant'] == 0
    original = json.loads(design.read_text())['modules']['Toy']
    candidate = json.loads((tmp_path/'analysis/optimized.json').read_text())['modules']['Toy']
    assert original['ports'] == candidate['ports'] and original['netnames'] == candidate['netnames']
    cell_name = report['accepted'][0]['cell']
    assert [n for n in original['cells'] if original['cells'][n]!=candidate['cells'][n]] == [cell_name]
    # The old predicate is not constant: a/b remain unrestricted. The internal
    # hidden FF can diverge, so requiring continuing state equality must fail.
    stronger = prove_pair(tmp_path/'analysis/reference.v',tmp_path/'analysis/optimized.v',
                          harness,'TemporalMiter',tmp_path/'stronger',yosys=YOSYS,smtbmc=SMTBMC,
                          solver='z3',depth=4,timeout=20,engine='pdr',abc=ABC,
                          assert_state_correspondence=True)
    assert not stronger['proven'] and 'pdr' in stronger


@integration
def test_visible_scalar_constants_rejected_and_final_original_reproved(tmp_path):
    design = elaborate(tmp_path,'''module Toy(input clk,input [1:0] a,b,output reg q);
      wire visible_eq = a == b;
      always @(posedge clk) q <= visible_eq;
    endmodule''')
    harness = tmp_path/'harness.sv'
    harness.write_text('''module TemporalMiter(input clk);
      (* anyseq *) reg [1:0] a,b;
      wire x,y; Toy reference(clk,a,b,x); ToyCandidate candidate(clk,a,b,y);
      always @* assert(x == y);
    endmodule''')
    report = analyze(design,harness,tmp_path/'analysis',scope='visible_eq')
    assert report['accepted'] == [] and len(report['probes']) == 2
    assert all(not trial['proof']['proven'] for trial in report['probes'])
    assert json.loads((tmp_path/'analysis/optimized.json').read_text()) == json.loads(design.read_text())


@integration
@pytest.mark.parametrize('maximum',[1,8])
def test_cumulative_interaction_is_checked_against_original(tmp_path,maximum):
    design = elaborate(tmp_path,'''module Toy(input clk,input [1:0] a,b,c,d,output y);
      wire first_eq = a == b;
      wire second_eq = c == d;
      assign y = first_eq | second_eq;
    endmodule''')
    harness = tmp_path/'harness.sv'
    harness.write_text('''module TemporalMiter(input clk);
      (* anyseq *) reg [1:0] a,b,c,d;
      wire x,y; Toy reference(clk,a,b,c,d,x); ToyCandidate candidate(clk,a,b,c,d,y);
      always @* begin assume(a==b); assume(c==d); assert(x == y); end
    endmodule''')
    report = analyze(design,harness,tmp_path/'analysis',maximum=maximum)
    if maximum == 1:
        assert len(report['accepted']) == len(report['probes']) == 1
        assert not report['search_complete'] and report['candidate_count'] == 4
        return
    assert len(report['accepted']) == 2
    assert [trial['candidate']['constant'] for trial in report['probes']] == [0,0,1]
    assert [trial['proof']['proven'] for trial in report['probes']] == [True,False,True]
    assert all(trial['proof']['reference_sha256'] == digest(tmp_path/'analysis/reference.v')
               for trial in report['probes'])
