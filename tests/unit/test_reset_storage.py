"""Small native-primitive tests for conditional reset storage and rewrites."""
import copy
import importlib.util
import json
from pathlib import Path
import shutil
import sys

import pytest

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
SPEC=importlib.util.spec_from_file_location('reset_storage',ROOT/'experiments/bounded_dynamic/len5/application_screen/reset_storage.py')
r=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(r)

HEADER='''module arith_rs #(parameter DEPTH=2)(
 input logic clk_i, input logic rst_ni, input logic flush_i,
 input logic issue_valid_i, input logic new_idx, input logic [1:0] value_i);
 typedef logic [1:0] row_data_t;
 row_data_t [DEPTH-1:0] data;
 logic [DEPTH-1:0] curr_state, next_state;
endmodule
'''


def cell(kind, con, params):
    return {'type':kind,'hide_name':0,'attributes':{},'parameters':params,
            'connections':con,'port_directions':{n:'output' if n in ('Y','Q') else 'input' for n in con}}


@pytest.fixture
def toy():
    ports={n:{'direction':'input','bits':bits} for n,bits in
        [('clk_i',[2]),('rst_ni',[3]),('flush_i',[4]),('issue_valid_i',[5]),('new_idx',[6]),('value_i',[7,8])]}
    q=list(range(100,106));d=[202,203,212,213,206,216]
    cells={'storage':cell('$aldff',{'CLK':[2],'ALOAD':[3],'AD':['0']*6,'D':d,'Q':q},
                        {'WIDTH':6,'CLK_POLARITY':1,'ALOAD_POLARITY':0})}
    for i in range(2):
        base=200+10*i
        cells[f'index{i}']=cell('$eq',{'A':[6],'B':[str(i)],'Y':[base]},
            {'A_WIDTH':1,'B_WIDTH':1,'Y_WIDTH':1,'A_SIGNED':0,'B_SIGNED':0})
        cells[f'admit{i}']=cell('$and',{'A':[5],'B':[base],'Y':[base+1]},
            {'A_WIDTH':1,'B_WIDTH':1,'Y_WIDTH':1,'A_SIGNED':0,'B_SIGNED':0})
        cells[f'data{i}']=cell('$mux',{'A':q[2*i:2*i+2],'B':[7,8],'S':[base+1],'Y':[base+2,base+3]}, {'WIDTH':2})
        cells[f'state{i}']=cell('$mux',{'A':[q[4+i]],'B':['1'],'S':[base+1],'Y':[base+4]}, {'WIDTH':1})
        cells[f'flush{i}']=cell('$mux',{'A':[base+4],'B':['0'],'S':[4],'Y':[base+6]}, {'WIDTH':1})
        cells[f'empty{i}']=cell('$not',{'A':[q[4+i]],'Y':[300+i]}, {'A_WIDTH':1,'Y_WIDTH':1,'A_SIGNED':0})
    nets={r.PREFIX+n:{'bits':p['bits'],'attributes':{},'hide_name':0} for n,p in ports.items()}
    for name,bits in [('insert',[5]),('data',q[:4]),('curr_state',q[4:]),('empty',[300,301])]:
        nets[r.PREFIX+name]={'bits':bits,'attributes':{},'hide_name':0}
    ports['payload_debug']={'direction':'output','bits':q[:4]}
    return {'modules':{'datapath':{'ports':ports,'netnames':nets,'cells':cells}}}


def test_exact_partial_ff_slice_and_input_boundary(toy):
    before=copy.deepcopy(toy);p,a=r.project_row(toy,0,HEADER)
    assert toy==before and a['ff_bits']==3 and a['selected_ff_slices'][0]['indices']==[0,1,4]
    ff=p['modules']['NativeRow']['cells']['storage']
    assert ff['connections']['Q']==[100,101,104] and ff['connections']['D']==[202,203,206]
    assert ff['connections']['AD']==['0']*3 and int(ff['parameters']['WIDTH'],2)==3
    assert a['insert_bits']==[5] and a['index_bits']==[6]
    assert 'numeric row0' in a['numeric_row_binding']


@pytest.mark.parametrize('change',['init','unsupported_ff','dynamic_reset','cut_q_collision','cut_driver_collision','ascending_rows'])
def test_unsupported_or_unsound_projections_fail_closed(toy,change):
    m=toy['modules']['datapath'];header=HEADER
    if change=='init':m['netnames'][r.PREFIX+'data']['attributes']['init']='0000'
    elif change=='unsupported_ff':m['cells']['storage']['type']='$dff'
    elif change=='dynamic_reset':m['cells']['storage']['connections']['AD'][0]=7
    elif change=='cut_q_collision':m['netnames'][r.PREFIX+'value_i']['bits'][0]=100
    elif change=='cut_driver_collision':m['netnames'][r.PREFIX+'value_i']['bits'][0]=202
    else:header=header.replace('[DEPTH-1:0]','[0:DEPTH-1]')
    with pytest.raises(ValueError):r.project_row(toy,0,header)


def test_adff_reset_parameter_slice_is_exact():
    c=cell('$adffe',{'CLK':[2],'ARST':[3],'EN':[4],'D':[10,11,12,13],'Q':[20,21,22,23]},
        {'WIDTH':4,'CLK_POLARITY':1,'ARST_POLARITY':0,'ARST_VALUE':'1010','EN_POLARITY':1})
    sliced,values=r.slice_reset_ff(c,[0,3])
    assert values==['0','1'] and sliced['parameters']['ARST_VALUE']=='10'
    assert sliced['connections']['D']==[10,13] and sliced['connections']['Q']==[20,23]
    assert sliced['connections']['EN']==[4] and c['parameters']['WIDTH']==4


def test_conditional_local_induction_negative_and_all_alias_rewrite(toy,tmp_path):
    yosys=shutil.which('yosys');smt=shutil.which('yosys-smtbmc')
    if not yosys or not smt or not shutil.which('z3'):pytest.skip('Yosys/smtbmc/Z3 required')
    before=copy.deepcopy(toy);projection,audit=r.project_row(toy,0,HEADER)
    proof=r.prove_local(projection,audit,tmp_path/'proof',yosys=yosys,smtbmc=smt,timeout=15)
    assert proof['status']=='conditional_reset_storage_proved',proof
    assert proof['proofs']['positive']['proven'] and proof['proofs']['negative']['counterexample_found']
    candidate,report=r.conditional_rewrite(toy,[proof]);m=candidate['modules']['datapath']
    assert toy==before and report['accepted_optimization'] is False and report['global_premise_discharged'] is False
    assert report['reset_constant_bits']==3 and report['sliced_native_ff_cells']==['storage']
    assert m['cells']['storage']['connections']['Q']==[102,103,105]
    assert m['cells']['storage']['connections']['D']==[212,213,216]
    assert m['ports']['payload_debug']['bits']==['0','0',102,103]
    assert m['netnames'][r.PREFIX+'curr_state']['bits']==['0',105]
    assert all(not {100,101,104}&set(bs) for c in m['cells'].values() for bs in c['connections'].values())
    # A genuine bounded pass, without induction evidence, cannot qualify.
    bounded=copy.deepcopy(proof);bounded['proofs']['positive'].pop('induction')
    with pytest.raises(ValueError,match='bounded pass'):r.conditional_rewrite(toy,[bounded])
    source=tmp_path/'proof/projection.json';source.write_bytes(source.read_bytes()+b'\n')
    with pytest.raises(ValueError,match='evidence changed'):r.conditional_rewrite(toy,[proof])


def test_admission_while_held_in_reset_is_allowed_and_storage_stays_reset(toy,tmp_path):
    yosys=shutil.which('yosys');smt=shutil.which('yosys-smtbmc')
    if not yosys or not smt or not shutil.which('z3'):pytest.skip('Yosys/smtbmc/Z3 required')
    projection,audit=r.project_row(toy,0,HEADER)
    native=tmp_path/'native.json';native.write_text(json.dumps(projection))
    # Cover must be reachable, not merely an assertion proved in an empty domain.
    monitor=tmp_path/'harness.sv'
    monitor.write_text(r.harness(projection,audit).replace('endmodule',
        'always @* begin assume(!rst_ni); assume(insert_i); assume(new_index_i == 0); cover(insert_i); end\nendmodule'))
    model=tmp_path/'model.smt2'
    r.checked_yosys(yosys,f'read_json {r.yosys_path(native)}\nsetundef -anyseq\n'
        f'read_verilog -formal -sv {r.yosys_path(monitor)}\n'+r.formal_prepare_command('ResetStorageProof')+
        r.formal_lower_command(yosys)+'async2sync\ndffunmap\nsetundef -anyseq\n'+
        f'write_smt2 -wires {r.yosys_path(model)}\n',tmp_path,'export',15)
    base=r.run_command([smt,'-s','z3','-t','3',str(model)],tmp_path/'base.log',15)
    cover=r.run_command([smt,'-s','z3','-t','3','-c',str(model)],tmp_path/'cover.log',15)
    assert r.proof_passed(base) and r.proof_passed(cover)
    assert 'Reached cover statement' in (tmp_path/'cover.log').read_text()
