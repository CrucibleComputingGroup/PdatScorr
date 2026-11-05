"""Undefined choices must survive frontend optimization until formal solving."""
import json
from pathlib import Path
import shutil
import sys

import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from odc.temporal import (checked_yosys, export_design, formal_lower_command,
                          formal_prepare_command, proof_passed, prove_pair, run_command)

YOSYS = shutil.which('yosys')
SMTBMC = shutil.which('yosys-smtbmc')
ABC = shutil.which('abc') or shutil.which('yosys-abc')
pytestmark = pytest.mark.skipif(not all((YOSYS, SMTBMC, ABC, shutil.which('z3'))),
                               reason='Yosys, smtbmc, ABC and Z3 required')


def pair(tmp_path, body, *, assumption=''):
    reference, candidate, harness = (tmp_path/name for name in ('reference.v','candidate.v','harness.sv'))
    reference.write_text('module Ref(input s,d,output reg y); '+body+' endmodule\n')
    candidate.write_text('module Cand(input s,d,output y); assign y=d; endmodule\n')
    harness.write_text('''module M(input s,d);
      wire a,b; Ref reference(s,d,a); Cand candidate(s,d,b);
      always @* begin '''+assumption+''' assert(a==b); end
    endmodule\n''')
    return reference,candidate,harness


def prove(paths, directory, engine):
    return prove_pair(*paths,'M',directory,yosys=YOSYS,smtbmc=SMTBMC,solver='z3',
                      depth=3,timeout=20,engine=engine,abc=ABC,
                      match_initial_state=False,assert_state_correspondence=False)


@pytest.mark.parametrize('body',[
    "always @* y = s ? 1'bx : d;",
    "always @* case(s) 1'b0:y=d; default:y=1'bx; endcase",
])
@pytest.mark.parametrize('engine',['induction','pdr'])
def test_original_x_mux_choice_cannot_be_constantized_away(tmp_path,body,engine):
    paths=pair(tmp_path,body,assumption='assume(!d);')
    # The previous SMT path did not symbolize residual X at all: write_smt2
    # emitted #b0. Reproduce its false base AND induction certificate, then
    # require an explicit counterexample under both fixed proof engines.
    legacy_smt=tmp_path/'legacy.smt2'
    legacy=checked_yosys(YOSYS,
        'read_verilog -formal -sv '+ ' '.join('"'+str(p)+'"' for p in paths)+'\n'
        'prep -top M -flatten\n'+formal_lower_command(YOSYS)+
        f'async2sync\ndffunmap\nwrite_smt2 "{legacy_smt}"\n',tmp_path,'legacy',20)
    command=[SMTBMC,'-s','z3','-t','3','--noprogress']
    base=run_command(command+[str(legacy_smt)],tmp_path/'legacy_base.log',20)
    step=run_command(command+['-i',str(legacy_smt)],tmp_path/'legacy_step.log',20)
    assert proof_passed(base) and proof_passed(step)
    result=prove(paths,tmp_path/'fixed',engine)
    assert not result['proven'],result
    assert 'error' not in result,result
    if engine=='pdr':
        assert 'was asserted' in Path(result['pdr']['log']).read_text()
    else:
        assert 'Assert failed' in Path(result['base']['log']).read_text()
    cells=json.loads((tmp_path/'fixed/miter.json').read_text())['modules']['M']['cells']
    assert any(c['type']=='$anyseq' for c in cells.values())
    assert not any(x in ('x','z') for c in cells.values()
                   for bs in c['connections'].values() for x in bs)


@pytest.mark.parametrize('engine',['induction','pdr'])
def test_unobservable_x_choice_still_allows_valid_equivalence(tmp_path,engine):
    paths=pair(tmp_path,"always @* y=s?1'bx:d;",assumption='assume(!s);')
    result=prove(paths,tmp_path/'fixed',engine)
    assert result['proven'],result
    assert result['property_counts']['assume']==1


def test_casez_pattern_is_not_changed_into_a_symbolic_data_choice(tmp_path):
    reference,candidate,harness=(tmp_path/n for n in ('reference.v','candidate.v','harness.sv'))
    reference.write_text("module Ref(input [1:0] s,input d,output reg y); always @* casez(s) 2'b?0:y=d; default:y=0; endcase endmodule\n")
    candidate.write_text("module Cand(input [1:0] s,input d,output y); assign y=s[0]?1'b0:d; endmodule\n")
    harness.write_text('module M(input [1:0] s,input d); wire a,b; Ref reference(s,d,a); Cand candidate(s,d,b); always @* assert(a==b); endmodule\n')
    result=prove((reference,candidate,harness),tmp_path/'fixed','pdr')
    assert result['proven'],result


def test_json_to_verilog_export_preserves_native_unknown_connections(tmp_path):
    paths=pair(tmp_path,"always @* y=s?1'bx:d;")
    source=tmp_path/'source.json'
    checked_yosys(YOSYS,f'read_verilog "{paths[0]}"\nhierarchy -top Ref\nproc -noopt -norom\nwrite_json "{source}"\n',tmp_path,'source',20)
    design=json.loads(source.read_text())
    assert any('x' in bs for c in design['modules']['Ref']['cells'].values() for bs in c['connections'].values())
    exported=tmp_path/'exported.v'
    export_design(design,'Ref','Ref',exported,YOSYS,20)
    result=prove((exported,paths[1],paths[2]),tmp_path/'fixed','pdr')
    assert not result['proven'] and 'was asserted' in Path(result['pdr']['log']).read_text()


def test_formal_preparation_rejects_nonordinary_top_identifiers():
    for name in ('bad-name','M; setundef -zero','M\nprep',''):
        with pytest.raises(ValueError,match='ordinary'):
            formal_prepare_command(name)
    script=formal_prepare_command('M')
    assert script.index('setundef -anyseq') < script.index('proc -norom -noopt') < script.index('prep -top')


@pytest.mark.parametrize('match_initial',[True,False])
def test_explicit_unknown_initial_value_remains_arbitrary_initial_state(tmp_path,match_initial):
    reference,candidate,harness=(tmp_path/n for n in ('reference.v','candidate.v','harness.sv'))
    reference.write_text("module Ref(input clk,d,output reg q=1'bx);always@(posedge clk)q<=d;endmodule\n")
    candidate.write_text("module Cand(input clk,d,output reg q=1'bx);always@(posedge clk)q<=d;endmodule\n")
    harness.write_text('module M(input clk,d);wire a,b;Ref reference(clk,d,a);Cand candidate(clk,d,b);always@*assert(a==b);endmodule\n')
    result=prove_pair(reference,candidate,harness,'M',tmp_path/'fixed',yosys=YOSYS,
        smtbmc=SMTBMC,solver='z3',depth=3,timeout=20,match_initial_state=match_initial)
    assert 'error' not in result,result
    assert result['proven'] == match_initial
    if match_initial:
        assert result['initial_state']['paired_state_bits']==1
    else:
        assert 'Assert failed' in Path(result['base']['log']).read_text()


@pytest.mark.parametrize('constrain_unknown',[False,True])
def test_native_state_certificate_wrapper_uses_safe_preparation(tmp_path,constrain_unknown):
    import importlib.util
    helper=ROOT/'experiments/bounded_dynamic/len5/phase_sharing/proof.py'
    spec=importlib.util.spec_from_file_location('safe_native_proof',helper)
    native=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(native)
    reference,candidate,harness=(tmp_path/n for n in ('reference.v','candidate.v','harness.sv'))
    body="input clk,rst_ni,s,d,output reg [1:0] q,output y); always@(posedge clk or negedge rst_ni)if(!rst_ni)q<=0;else q<=q+1;"
    reference.write_text('module Ref('+body+"assign y=s?1'bx:d;endmodule\n")
    candidate.write_text('module Cand('+body+'assign y=d;endmodule\n')
    harness.write_text('''module BankMiter(input clk,rst_ni,s,d);
      wire [1:0] qa,qb;wire a,b;
      Ref reference(clk,rst_ni,s,d,qa,a);Cand candidate(clk,rst_ni,s,d,qb,b);
      always@*begin if($initstate)assume(!rst_ni);assume(!d);'''+
      ('assume(!s);' if constrain_unknown else '')+'''assert(qa==qb);assert(a==b);end
    endmodule\n''')
    result=native.prove(reference,candidate,harness,tmp_path/'fixed',yosys=YOSYS,depth=3,timeout=20)
    assert 'error' not in result,result
    assert result['proven']==constrain_unknown
    assert result['native_state_certificates']['asserted_state_pairs']==2
    assert result['state_assumptions_added']==0 and not result['initial_pairing']
    assert (tmp_path/'fixed/temporal_source.py').read_bytes()==(ROOT/'odc/temporal.py').read_bytes()
    if not constrain_unknown:
        assert 'Assert failed' in Path(result['base']['log']).read_text()
