#!/usr/bin/env python3
"""Source-bound native EU register and MUL/DIV dispatch lemmas, without timing."""
import argparse
import copy
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE.parents[3]),str(HERE)]
from odc.temporal import (checked_yosys,digest,formal_lower_command,formal_prepare_command,
    proof_passed,run_command,validate_single_clock,yosys_path)
from eu_domain_diagnostic import native_path,require
from reset_storage import slice_reset_ff


def read(path):return json.loads(Path(path).read_text())


def register_projection(path):
    cells=copy.deepcopy(path['native_high_bit_data_mux_slices'])
    item=path['ireg_assigned_eu_ff'];ff,reset=slice_reset_ff(item['cell'],[2])
    require(reset==['0'] and ff['connections']['Q']==[path['ireg_high_bit']], 'Native visible high/reset binding changed')
    cells[item['name']]=ff
    ports={'clk_i':{'direction':'input','bits':ff['connections']['CLK']},
           'rst_ni':{'direction':'input','bits':ff['connections']['ALOAD']},
           'decoded_high':{'direction':'input','bits':[path['decoder_assigned_eu_bits'][2]]},
           'controls':{'direction':'input','bits':path['arbitrary_control_cut_candidates']},
           'visible_high':{'direction':'output','bits':[path['ireg_high_bit']]}}
    inputs=[bit for p in ports.values() if p['direction']=='input' for bit in p['bits']]
    require(len(inputs)==len(set(inputs)),'Register projection input alias collision')
    driven={bit for c in cells.values() for p,d in c['port_directions'].items() if d=='output' for bit in c['connections'][p]}
    require(not set(inputs)&driven,'Register projection has a cut/driver collision')
    require(all(type(bit)is not int or bit in set(inputs)|driven for c in cells.values()
                for p,d in c['port_directions'].items() if d=='input' for bit in c['connections'][p]),'Unbound native register fanin')
    return {'modules':{'NativeEURegister':{'attributes':{'top':'1'},'cells':cells,'ports':ports,
        'netnames':{name:{'bits':p['bits'],'hide_name':0,'attributes':{}} for name,p in ports.items()}}}}


def dispatch_projection(path):
    cells={**copy.deepcopy(path['native_onehot_demux']),**copy.deepcopy(path['native_dispatch_and'])}
    selected=path['ireg_assigned_eu_ff']['cell']['connections']['Q']
    driven={bit for c in cells.values() for pin,d in c['port_directions'].items() if d=='output' for bit in c['connections'][pin] if type(bit)is int}
    extra=sorted({bit for c in cells.values() for pin,d in c['port_directions'].items() if d=='input'
                  for bit in c['connections'][pin] if type(bit)is int and bit not in driven and bit not in selected})
    ports={'registered_eu':{'direction':'input','bits':selected},'other_inputs':{'direction':'input','bits':extra},
           'mul_valid':{'direction':'output','bits':[path['mul_issue_valid_bit']]},
           'div_valid':{'direction':'output','bits':[path['div_issue_valid_bit']]}}
    require(len(extra)>0 and not driven&set(selected+extra),'Invalid native dispatch boundary')
    return {'modules':{'NativeEUDispatch':{'attributes':{'top':'1'},'cells':cells,'ports':ports,
        'netnames':{name:{'bits':p['bits'],'hide_name':0,'attributes':{}} for name,p in ports.items()}}}}


def proof_harness(design, *, derived_premise, sequential):
    top=next(iter(design['modules']));ports=design['modules'][top]['ports']
    declarations=[f'input [{len(p["bits"])-1}:0] {n}' for n,p in ports.items() if p['direction']=='input']
    declarations+=[f'output [{len(p["bits"])-1}:0] {n}' for n,p in ports.items() if p['direction']=='output']
    lines=['module EUProof('+', '.join(declarations)+');',top+' dut('+', '.join(f'.{n}({n})' for n in ports)+');','always @* begin']
    if sequential:lines.append('if ($initstate) assume(!rst_ni);')
    if derived_premise:lines.append('assume(decoded_high == 0);' if sequential else 'assume(registered_eu[2] == 0);')
    lines.append('assert(visible_high == 0);' if sequential else 'assert(!mul_valid && !div_valid);')
    return '\n'.join(lines+['end','endmodule',''])


def run_proof(design,out,*,yosys,derived_premise=True,sequential=True):
    out.mkdir();native=out/'native.json';native.write_text(json.dumps(design)+'\n')
    monitor=out/'harness.sv';monitor.write_text(proof_harness(design,derived_premise=derived_premise,sequential=sequential))
    script=f'read_json {yosys_path(native)}\nsetundef -anyseq\nbwmuxmap\nbmuxmap\ndemuxmap\nsetundef -anyseq\n'
    script+=f'read_verilog -formal -sv {yosys_path(monitor)}\n'+formal_prepare_command('EUProof')+formal_lower_command(yosys)
    if sequential:script+='async2sync\ndffunmap\n'
    script+='setundef -anyseq\ncheck -assert\n'+f'write_json {yosys_path(out/"lowered.json")}\n'
    result={'status':'unproved','sequential':sequential,'derived_premise_present':derived_premise}
    if sequential:
        script+=f'write_smt2 -wires {yosys_path(out/"model.smt2")}\n'
        result['export']=checked_yosys(yosys,script,out,'export',20)
        model=out/'model.smt2';smt=str(Path(yosys).with_name('yosys-smtbmc'))
        result['clock_model']=validate_single_clock(read(out/'lowered.json'),'EUProof')
        args=[smt,'-s','z3','-t','4','--noprogress']
        result['base']=run_command(args+['--dump-vcd',str(out/'counterexample.vcd'),str(model)],out/'base.log',20)
        if proof_passed(result['base']):
            result['induction']=run_command(args+['-i',str(model)],out/'induction.log',20)
            if proof_passed(result['induction']):result['status']='proved_unbounded'
        elif result['base']['returncode']==1 and not result['base']['timeout'] and 'Status: FAILED' in (out/'base.log').read_text() and (out/'counterexample.vcd').exists():
            result['status']='counterexample_found'
        result['smt_sha256']=digest(model)
    else:
        script+=f'tee -o {yosys_path(out/"sat.log")} sat -set-assumes -prove-asserts -show registered_eu -show mul_valid -show div_valid -dump_vcd {yosys_path(out/"counterexample.vcd")}\n'
        result['execution']=checked_yosys(yosys,script,out,'check',20);text=(out/'sat.log').read_text()
        success=text.count('SAT proof finished - no model found: SUCCESS!');failure=text.count('SAT proof finished - model found: FAIL!')
        require(success+failure==1 and 'ERROR' not in text,'Unknown dispatch SAT result')
        result['status']='proved_combinationally' if success else 'counterexample_found'
        result['sat_log_sha256']=digest(out/'sat.log')
    lowered=read(out/'lowered.json')['modules']['EUProof']
    require(not any(bit in ('x','z') for c in lowered['cells'].values() for bs in c['connections'].values() for bit in bs),'Undefined literal in final model')
    result['property_counts']={kind:sum(c['type']=='$'+kind for c in lowered['cells'].values()) for kind in ('assert','assume')}
    require(result['property_counts']=={'assert':1,'assume':int(sequential)+int(derived_premise)},'Unexpected proof premises')
    result['native_json_sha256']=digest(native);result['lowered_json_sha256']=digest(out/'lowered.json')
    result['harness_sha256']=digest(monitor)
    (out/'proof.json').write_text(json.dumps(result,indent=2)+'\n')
    return result


def verify_decoder_dependency(certificate_path,diagnostic,certifier,out):
    certificate=read(certificate_path);require(digest(certifier)==certificate['certifier_sha256'],'Changed closed-certificate verifier')
    require(certificate['status']=='component_equivalence_and_domain_propagation_certified' and certificate['domain']=='program_alphabet', 'Unsupported decoder certificate')
    prepared=Path(certificate['native_original_json']).parent;candidate=Path(certificate['candidate_summary']).parent
    replay=out/'replayed_decoder_certificate.json'
    command=[sys.executable,str(certifier),'--prepared',str(prepared),'--candidate',str(candidate),
             '--domain-proof',str(Path(certificate['domain_summary']).parent),'--pair-recheck',str(Path(certificate['paired_proof_summary']).parent),'--output',str(replay)]
    execution=run_command(command,out/'certificate_replay.log',30)
    require(execution['returncode']==0 and not execution['timeout'] and replay.exists() and read(replay)==certificate,'Closed decoder certificate replay failed')
    report=read(diagnostic/'summary.json');test=report['tests']['candidate_unrestricted'];part=diagnostic/'candidate_unrestricted'
    require(test['status']=='proved_combinationally' and test['domain_expression'] is None,'Unconditional candidate decoder theorem missing')
    require(digest(part/'decoder.json')==test['input_json_sha256'] and digest(part/'lowered.json')==test['lowered_json_sha256'], 'Decoder theorem model changed')
    require(digest(part/'sat.log')==test['proof_log_sha256'] and test['execution']['returncode']==0 and not test['execution']['timeout'],'Decoder SAT result changed')
    require((part/'sat.log').read_text().count('SAT proof finished - no model found: SUCCESS!')==1,'Decoder SAT did not prove')
    lowered=read(part/'lowered.json')['modules']['EUDomainProof']
    require(lowered['ports']['assigned_eu']['bits'][2]=='0' and not any(c['type']=='$assume' for c in lowered['cells'].values()), 'Decoder premise is not unconditional')
    original=read(certificate['native_original_json']);modified=read(certificate['native_candidate_json'])
    component=read(part/'decoder.json')['modules']['DecoderBase'];native=modified['modules']['datapath']
    require(component['ports']['assigned_eu_o']['bits']==native['netnames']['u_backend.u_issue_stage.id_assigned_eu']['bits'],'Derived decoder bit binding changed')
    require(all(cell==native['cells'][name] for name,cell in component['cells'].items()),'Decoder proof component differs from certified candidate')
    for path,sha in report['source_sha256'].items():require(digest(Path(path))==sha,'Diagnostic source changed')
    expected='module EUDomainProof(input [31:0] instruction_i, output [2:0] assigned_eu);\nDecoderBase dut(.instruction_i(instruction_i), .assigned_eu_o(assigned_eu));\nalways @* begin\nassert(assigned_eu[2] == 0);\nend\nendmodule\n'
    require((part/'harness.sv').read_text()==expected,'Decoder theorem harness premises changed')
    return original,modified,certificate,{'certificate_sha256':digest(certificate_path),'diagnostic_summary_sha256':digest(diagnostic/'summary.json'),
        'sat_log_sha256':test['proof_log_sha256'],'decoder_model_sha256':test['lowered_json_sha256'],'certificate_replay':execution}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--certificate',type=Path,required=True)
    p.add_argument('--diagnostic',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--yosys',required=True)
    args=p.parse_args();out=args.output.resolve();out.mkdir(parents=True,exist_ok=False)
    certifier=HERE.parent/'isa_baseline/certify.py'
    before_certificate=read(args.certificate)
    dependency_paths=[args.certificate.resolve(),args.diagnostic.resolve()/'summary.json',certifier,Path(__file__),
                      HERE/'eu_domain_diagnostic.py',HERE/'reset_storage.py',Path(before_certificate['native_original_json']),Path(before_certificate['native_candidate_json'])]
    starting_hashes={str(p):digest(p) for p in dependency_paths}
    original,candidate,certificate,dependency=verify_decoder_dependency(args.certificate.resolve(),args.diagnostic.resolve(),certifier,out)
    path=native_path(original['modules']['datapath']);require(path==native_path(candidate['modules']['datapath']),'Native pipeline changed by decoder substitution')
    register=register_projection(path);dispatch=dispatch_projection(path)
    results={}
    for name,design,sequential,derived in [('register',register,True,True),('register_negative',register,True,False),
        ('dispatch',dispatch,False,True),('dispatch_negative',dispatch,False,False)]:
        results[name]=run_proof(design,out/name,yosys=args.yosys,sequential=sequential,derived_premise=derived)
    success=results['register']['status']=='proved_unbounded' and results['dispatch']['status']=='proved_combinationally'
    require(results['register_negative']['status']=='counterexample_found' and results['dispatch_negative']['status']=='counterexample_found','Negative controls failed to expose removed premise')
    require(all(digest(Path(p))==sha for p,sha in starting_hashes.items()),'Proof dependency changed during run')
    path['pipeline_theorem_status']='Native visible register invariant and exact dispatch consequences proved in this run' if success else 'Unproved'
    record={'status':'native_register_and_dispatch_lemmas_proved' if success else 'unproved','accepted_optimization':False,
        'classification':'Pscorr program-only derived native facts; no timing premise or hardware rewrite',
        'external_premises':certificate['external_premises'],'new_environmental_premises':[],
        'native_visible_register_high_bit':path['ireg_high_bit'],'native_decoder_high_bit':path['decoder_assigned_eu_bits'][2],
        'native_mul_issue_valid_bit':path['mul_issue_valid_bit'],'native_div_issue_valid_bit':path['div_issue_valid_bit'],
        'path':path,'decoder_dependency':dependency,'proofs':results,
        'dependency_sha256':starting_hashes,
        'composition':'Closed decoder equivalence and native input-domain proof imply original/candidate correspondence under the external program-word domain. The exact certified candidate decoder has unconditional high-bit zero. The original one-bit visible issue-register projection proves reset-preserved high-bit zero for arbitrary shared native enable/flush controls. Exact native onehot-decode/valid-AND then proves both MUL/DIV issue valids zero. The local assumptions are discharged by preceding proved conclusions, not perpetual-idle premises. Removing FU state/output cones still requires further native reset/output closure.'}
    (out/'eu_register_lemma_source.py').write_bytes(Path(__file__).read_bytes())
    (out/'summary.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({k:v['status'] for k,v in results.items()}))
    return 0 if success else 1


if __name__=='__main__':raise SystemExit(main())
