"""Bank compatibility is a filter; actual lifetime safety requires equivalence."""
import copy
import json
from pathlib import Path
import shutil
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from odc.bank_sharing import bank_candidates, merge_banks, filter_exclusive_writes
from odc.temporal import export_design, prove_pair

MODERN = ROOT.parents[2]/'tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys'
YOSYS = str(MODERN) if MODERN.is_file() else shutil.which('yosys')
ABC = shutil.which('abc') or shutil.which('yosys-abc')
SMTBMC = shutil.which('yosys-smtbmc')
integration = pytest.mark.skipif(not all((YOSYS,ABC,SMTBMC)),reason='Yosys/ABC required')


def fixture():
    def bank(d,q,polarity):
        return {'type':'$adffe','attributes':{},
                'parameters':{'WIDTH':'100','CLK_POLARITY':'1','EN_POLARITY':str(polarity),
                              'ARST_POLARITY':'1','ARST_VALUE':'0000'},
                'connections':{'CLK':[2],'ARST':[3],'EN':[4],'D':d,'Q':q},
                'port_directions':{'CLK':'input','ARST':'input','EN':'input','D':'input','Q':'output'}}
    return {'modules':{'Toy':{
        'ports':{'clk':{'direction':'input','bits':[2]},'rst':{'direction':'input','bits':[3]},
                 'select':{'direction':'input','bits':[4]},
                 'da':{'direction':'input','bits':[6,7,8,9]},
                 'db':{'direction':'input','bits':[10,11,12,13]},
                 'qa':{'direction':'output','bits':[20,21,22,23]},
                 'qb':{'direction':'output','bits':[24,25,26,27]}},
        'netnames':{'a':{'bits':[20,21,22,23],'attributes':{}},
                    'b':{'bits':[24,25,26,27],'attributes':{}}},
        'cells':{'a':bank([6,7,8,9],[20,21,22,23],0),
                 'b':bank([10,11,12,13],[24,25,26,27],1)}}}}


def test_polarity_reset_and_q_alias_rewrite_are_preserved():
    design = fixture(); before = copy.deepcopy(design)
    candidates = bank_candidates(design,'Toy')
    assert len(candidates)==1 and candidates[0]['status']=='candidate_unproved'
    changed = merge_banks(design,'Toy',candidates[0])['modules']['Toy']
    original = design['modules']['Toy']
    assert design == before
    assert 'b' not in changed['cells']
    assert changed['cells']['a']['connections']['Q'] == original['cells']['a']['connections']['Q']
    for key in ('CLK','ARST'):
        assert changed['cells']['a']['connections'][key] == original['cells']['a']['connections'][key]
    for key in ('WIDTH','CLK_POLARITY','ARST_POLARITY','ARST_VALUE'):
        assert changed['cells']['a']['parameters'][key] == original['cells']['a']['parameters'][key]
    prefix = '$pscorr_share_'+candidates[0]['id']
    assert changed['cells'][prefix+'_ena']['connections']['A'] == [4]
    assert prefix+'_enb' not in changed['cells']
    mux = changed['cells'][prefix+'_data']['connections']
    assert mux['S']==[4] and mux['A']==[6,7,8,9] and mux['B']==[10,11,12,13]
    assert changed['netnames']['b']['bits'] == changed['netnames']['a']['bits']
    assert changed['ports']['qb']['bits'] == changed['ports']['qa']['bits']
    for name,port in original['ports'].items():
        if port['direction']=='input':
            assert changed['ports'][name] == port


@pytest.mark.parametrize('field,value', [('CLK_POLARITY','0'),('ARST_POLARITY','0'),('ARST_VALUE','1111')])
def test_different_clock_or_reset_parameters_are_not_candidates(field,value):
    design=fixture();design['modules']['Toy']['cells']['b']['parameters'][field]=value
    assert bank_candidates(design,'Toy') == []


def test_explicit_initial_values_must_agree_between_banks():
    design=fixture(); nets=design['modules']['Toy']['netnames']
    nets['a']['attributes']['init']='0000';nets['b']['attributes']['init']='1111'
    assert bank_candidates(design,'Toy') == []


def test_mutator_rechecks_changed_initial_values():
    design=fixture();candidate=bank_candidates(design,'Toy')[0]
    nets=design['modules']['Toy']['netnames']
    nets['a']['attributes']['init']='0000';nets['b']['attributes']['init']='1111'
    with pytest.raises(ValueError,match='Incompatible explicit initial'):
        merge_banks(design,'Toy',candidate)


def test_conflicting_initial_aliases_are_rejected():
    design=fixture();nets=design['modules']['Toy']['netnames']
    nets['a']['attributes']['init']='0000'
    nets['a_alias']={'bits':list(nets['a']['bits']),'attributes':{'init':'1111'}}
    nets['b']['attributes']['init']='1111'
    with pytest.raises(ValueError,match='[Ii]nit|[Cc]onflict'):
        bank_candidates(design,'Toy')


@integration
def test_write_exclusion_filter_rejects_simultaneous_enables(tmp_path):
    design=fixture()
    design['modules']['Toy']['cells']['a']['parameters']['EN_POLARITY']='1'
    candidates=bank_candidates(design,'Toy')
    assert len(candidates)==1
    result=filter_exclusive_writes(design,'Toy',candidates,tmp_path/'overlap',yosys=YOSYS,timeout=20)
    assert result['candidates'][0]['exclusive_writes'] is False


def elaborate(folder,overlapping):
    source=folder/'banks.sv';design=folder/'banks.json'
    output='output [7:0] q' if overlapping else 'output [3:0] q'
    expression='{a,b}' if overlapping else 'selected ? b : a'
    source.write_text(f'''module Toy(input clk,rst,select,input [3:0] da,db,{output});
      reg [3:0] a,b;
      reg selected;
      always @(posedge clk or posedge rst) begin
        if (rst) a <= 0; else if (!select) a <= da;
      end
      always @(posedge clk or posedge rst) begin
        if (rst) b <= 0; else if (select) b <= db;
      end
      always @(posedge clk or posedge rst) begin
        if (rst) selected <= 0; else selected <= select;
      end
      assign q = {expression};
    endmodule''')
    result=subprocess.run([YOSYS,'-Q','-T','-p',
        f'read_verilog -sv "{source}"; hierarchy -top Toy; proc; opt; write_json "{design}"'],
        text=True,capture_output=True,timeout=30)
    assert result.returncode==0,result.stdout+result.stderr
    return json.loads(design.read_text())


@integration
@pytest.mark.parametrize('overlapping,wrong_priority,expected',[
    (False,False,True),(True,False,False),(False,True,False)])
def test_exclusive_write_filter_needs_real_lifetime_proof(tmp_path,overlapping,wrong_priority,expected):
    design=elaborate(tmp_path,overlapping)
    candidates=bank_candidates(design,'Toy',min_width=4)
    assert len(candidates)==1
    excluded=filter_exclusive_writes(design,'Toy',candidates,tmp_path/'exclusive',yosys=YOSYS,timeout=20)
    assert excluded['candidates'][0]['exclusive_writes']
    changed=merge_banks(design,'Toy',candidates[0],wrong_priority=wrong_priority)
    reference,modified=tmp_path/'reference.v',tmp_path/'candidate.v'
    export_design(design,'Toy','Toy',reference,YOSYS,20)
    export_design(changed,'Toy','ToyCandidate',modified,YOSYS,20)
    width=8 if overlapping else 4
    harness=tmp_path/'harness.sv'
    harness.write_text(f'''module TemporalMiter(input clk);
      (* anyseq *) reg rst,select;
      (* anyseq *) reg [3:0] da,db;
      wire [{width-1}:0] a,b;
      Toy reference(clk,rst,select,da,db,a);
      ToyCandidate candidate(clk,rst,select,da,db,b);
      reg first_cycle=1;
      always @(posedge clk) first_cycle<=0;
      always @* begin
        if(first_cycle) assume(rst);
        assert(a==b);
      end
    endmodule''')
    result=prove_pair(reference,modified,harness,'TemporalMiter',tmp_path/'proof',
                      yosys=YOSYS,smtbmc=SMTBMC,solver='z3',depth=4,timeout=20,engine='pdr',abc=ABC,
                      assert_state_correspondence=False,match_initial_state=False)
    assert result['proven'] is expected,result
    assert result['initial_state']['paired_state_bits']==0
    assert 'pdr' in result
    if not expected:
        assert 'was asserted' in Path(result['pdr']['log']).read_text()
