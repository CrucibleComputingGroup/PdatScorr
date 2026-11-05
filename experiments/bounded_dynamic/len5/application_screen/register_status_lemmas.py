#!/usr/bin/env python3
"""Close native register-status reset facts using the proved RD-field domain.

This creates a query-only graph, never a hardware candidate or area result.
The original component, reset, flush, update controls, and functional read
ports remain intact in the local model. Only its two index domains are premises.
"""
from __future__ import annotations
import argparse
import copy
import json
import os
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
ISA=HERE.parent/'isa_baseline'
sys.path[:0]=[str(HERE.parents[3]),str(HERE),str(ISA),str(HERE.parent)]
from odc.temporal import (checked_yosys,digest,formal_lower_command,formal_prepare_command,
    parameter_int,proof_passed,run_command,validate_single_clock,yosys_path)
from domain_lemmas import check_unbounded_domain_proof,replay_domain_export
from prove_domain import data_projection

PREFIX='u_backend.u_int_regstat.'
INPUTS=('clk_i','rst_ni','flush_i','issue_valid_i','issue_rd_idx_i','issue_rob_idx_i',
    'issue_rs1_idx_i','issue_rs2_idx_i','comm_valid_i','comm_rd_idx_i')
OUTPUTS=('issue_rs1_busy_o','issue_rs1_rob_idx_o','issue_rs2_busy_o','issue_rs2_rob_idx_o')


def require(value,message):
    if not value: raise ValueError(message)


def read(path): return json.loads(Path(path).read_text())


def check_dependencies(dependencies):
    for path,expected in dependencies.items():
        require(digest(Path(path))==expected,'Source/proof dependency changed: '+path)


def native_component(original,allowed):
    module=original['modules']['datapath']
    ports={name:{'direction':'input' if name in INPUTS else 'output',
        'bits':list(module['netnames'][PREFIX+name]['bits'])} for name in (*INPUTS,*OUTPUTS)}
    boundary={b for name in INPUTS for b in ports[name]['bits']}
    require(sum(len(ports[name]['bits']) for name in INPUTS)==len(boundary),'Aliased native component inputs')
    drivers={}
    for name,cell in module['cells'].items():
        for pin,direction in cell['port_directions'].items():
            if direction=='output':
                for bit in cell['connections'][pin]:
                    if type(bit) is int:
                        require(bit not in drivers,'Multiple native drivers')
                        drivers[bit]=name
    selected=set();pending=[b for name in OUTPUTS for b in ports[name]['bits']]
    while pending:
        bit=pending.pop()
        if type(bit) is not int or bit in boundary:continue
        require(bit in drivers,'Undriven component cone')
        name=drivers[bit]
        if name in selected:continue
        selected.add(name)
        for pin,direction in module['cells'][name]['port_directions'].items():
            if direction=='input':pending.extend(module['cells'][name]['connections'][pin])
    states={n:module['cells'][n] for n in selected if 'ff' in module['cells'][n]['type'].lower()}
    require(len(states)==62 and sum(len(c['connections']['Q']) for c in states.values())==341,
            'Unexpected original register-status state inventory')
    entries=[]
    for index in range(1,32):
        if index in allowed:continue
        entry={'register':index,'fields':[]}
        for field,name,width in (
            ('count',f'$driver${PREFIX}gen_busy_counters[{index}].u_rob_cnt.count_o',6),
            ('tag',f'$driver${PREFIX}busy_rob_idx[{index}]',5)):
            cell=states[name];con=cell['connections'];par=cell['parameters']
            require(cell['type']=='$aldff' and len(con['Q'])==width and con['AD']==['0']*width,
                    'Selected state does not have an exact native zero asynchronous reset')
            require(con['CLK']==ports['clk_i']['bits']==module['ports']['clk_i']['bits']
                and con['ALOAD']==ports['rst_ni']['bits']==module['ports']['rst_ni']['bits']
                and parameter_int(par['CLK_POLARITY'])==1 and parameter_int(par['ALOAD_POLARITY'])==0,
                'Selected native state clock/reset differs from domain proof')
            output=f'{field}_{index}'
            ports[output]={'direction':'output','bits':list(con['Q'])}
            entry['fields'].append({'kind':field,'native_cell':name,'q_bits':list(con['Q']),
                'reset_bits':list(con['AD']),'proof_output':output})
        entries.append(entry)
    cells={name:copy.deepcopy(module['cells'][name]) for name in sorted(selected)}
    used={b for c in cells.values() for bits in c['connections'].values() for b in bits if type(b) is int}
    nets={name:copy.deepcopy(net) for name,net in module['netnames'].items()
        if name.startswith(PREFIX) and all(type(b) is not int or b in used|boundary for b in net['bits'])}
    nets.update({name:{'bits':list(port['bits']),'hide_name':0,'attributes':{}} for name,port in ports.items()})
    component={'modules':{'NativeRegisterStatus':{'attributes':{'top':'1'},'ports':ports,'netnames':nets,'cells':cells}}}
    return component,{'prefix':PREFIX,'native_component_cells':sorted(selected),'native_state_cells':sorted(states),
        'native_state_bits':341,'functional_input_bits':30,'functional_output_bits':12,
        'unused_entries':entries,'reset_bits':sum(len(f['q_bits']) for e in entries for f in e['fields'])}


def membership(name,values): return ' || '.join(f'({name} == 5\'d{value})' for value in values)


def harness(component,audit,values,*,relax=None):
    require(relax in (None,'issue','commit'),'Unknown negative-control premise')
    ports=component['modules']['NativeRegisterStatus']['ports']
    inputs=[f'input [{len(p["bits"])-1}:0] {n}' for n,p in ports.items() if p['direction']=='input']
    lines=['module RegisterStatusProof('+', '.join(inputs)+');']
    lines += [f'wire [{len(p["bits"])-1}:0] {n};' for n,p in ports.items() if p['direction']=='output']
    lines += ['NativeRegisterStatus dut('+', '.join(f'.{n}({n})' for n in ports)+');',
        'always @* begin','  if ($initstate) assume(!rst_ni);']
    if relax!='issue':lines.append('  assume('+membership('issue_rd_idx_i',values)+');')
    if relax!='commit':lines.append('  assume('+membership('comm_rd_idx_i',values)+');')
    for entry in audit['unused_entries']:
        for field in entry['fields']:lines.append(f'  assert({field["proof_output"]} == {len(field["q_bits"])}\'b0);')
    return '\n'.join(lines+['end','endmodule',''])


def replay_rd_chain(certificate_path,domain,original_rf,prepared_rf,pair,lowering,out,yosys):
    require(sys.flags.optimize==0 and os.environ.get('PYTHONOPTIMIZE','') in ('','0'),'Python assertions must remain enabled')
    certificate=read(certificate_path)
    require(certificate['status']=='decoder_and_register_specialization_composition_certified','Closed cumulative certificate required')
    parent_path=Path(certificate['decoder_certificate']);parent=read(parent_path)
    require(digest(ISA/'certify_registers.py')==certificate['certifier_sha256'],'RF certifier changed')
    require(digest(ISA/'certify.py')==parent['certifier_sha256'],'Decoder certifier changed')
    expected={**certificate['evidence_summary_sha256'],**certificate['proof_log_sha256'],
        str(parent_path):certificate['decoder_certificate_sha256']}
    original_path=Path(certificate['native_original_json']);candidate_path=Path(certificate['native_candidate_json'])
    require(digest(original_path)==certificate['native_original_sha256']==parent['native_original_sha256'],'Native original changed')
    require(digest(candidate_path)==certificate['native_candidate_sha256'],'Cumulative candidate changed')
    require(digest(domain/'summary.json')==certificate['evidence_summary_sha256'][str(domain/'summary.json')],'RD theorem is not certificate-bound')
    check_dependencies(expected)
    # Replay both source-bound certificate compositions; neither invokes a solver.
    commands=[
        [sys.executable,str(ISA/'certify.py'),'--prepared',str(original_path.parent),
         '--candidate',str(Path(parent['native_candidate_json']).parent),
         '--domain-proof',str(Path(parent['domain_summary']).parent),
         '--pair-recheck',str(Path(parent['paired_proof_summary']).parent),'--output',str(out/'decoder_certificate.json')],
        [sys.executable,str(ISA/'certify_registers.py'),'--decoder-certificate',str(parent_path),
         '--original-rf',str(original_rf),'--prepared-rf',str(prepared_rf),
         '--candidate',str(candidate_path.parent),'--domain-proof',str(domain),'--pair-recheck',str(pair),
         '--lowering-proof',str(lowering),'--output',str(out/'register_certificate.json')]]
    for name,command,record in zip(('decoder','register'),commands,(parent,certificate)):
        result=run_command(command,out/(name+'_certificate.log'),30)
        require(result['returncode']==0 and not result['timeout'],'Certificate composition replay failed: '+name)
        require(read(out/(name+'_certificate.json'))==record,'Fresh certificate differs: '+name)
    original,candidate=read(original_path),read(candidate_path)
    theorem=read(domain/'summary.json');projected=read(domain/'data_path.json')
    require(digest(ISA/'prove_domain.py')==theorem['source_sha256']==digest(domain/'prove_domain_source.py'),'RD projection source changed')
    reconstructed,audit=data_projection(original,theorem['projection']['target_net'],theorem['projection']['target_width'])
    require(reconstructed==projected and audit==theorem['projection'],'RD projection differs from exact original primitive slices')
    require(theorem['output_field_values']==[0,5,8,9,10,11,18] and theorem['instruction_field_low']==7,'Unexpected RD field domain')
    protected=set(audit['original_cell_slices'])|set(audit['retained_spill_write_control_cells'])
    require(all(original['modules']['datapath']['cells'][n]==candidate['modules']['datapath']['cells'][n] for n in protected),
            'Cumulative candidate changed a domain-proof primitive')
    ports=projected['modules']['InstructionDataPath']['ports']
    fields=audit['state_words']; require(len(fields)==40,'Expected40 original stored destination fields')
    issue=original['modules']['datapath']['netnames'][PREFIX+'issue_rd_idx_i']['bits']
    commit=original['modules']['datapath']['netnames'][PREFIX+'comm_rd_idx_i']['bits']
    require(ports['state_word_2']['bits']==issue and ports['state_word_0']['bits']==ports['decoder_word']['bits']==commit,
            'Register-status indices are not the actual proved fields')
    values=theorem['output_field_values']
    inputs=[f'input [{len(p["bits"])-1}:0] {n}' for n,p in ports.items() if p['direction']=='input']
    outputs=[n for n,p in ports.items() if p['direction']=='output']
    lines=['module DomainProof('+', '.join(inputs)+');']
    lines += [f'wire [4:0] {n};' for n in outputs]
    lines += ['InstructionDataPath dut('+', '.join(f'.{n}({n})' for n in ports)+');','always @* begin',
        '  if ($initstate) assume(!rst_ni);','  if (rst_ni && response_valid) assume('+parent['domain_expression']+');']
    lines += ['  assert('+membership(n,values)+');' for n in outputs]
    require((domain/'harness.sv').read_text()=='\n'.join(lines+['end','endmodule','']),'RD theorem harness changed')
    check_unbounded_domain_proof(theorem,domain)
    replay=replay_domain_export(domain,out/'rd_export_replay',yosys,30)
    model=read(domain/'lowered.json')['modules']['DomainProof']
    require(digest(domain/'lowered.json')==theorem['lowered_json_sha256'],'RD lowered source changed')
    require(sum(c['type']=='$assert' for c in model['cells'].values())==41 and
        sum(c['type']=='$assume' for c in model['cells'].values())==2,'RD property inventory changed')
    require(not any(b in ('x','z') for c in model['cells'].values() for bits in c['connections'].values() for b in bits),'RD literal undefined survived')
    return original,candidate,{'status':'closed_rd_chain_replayed','index_bindings':{'issue':issue,'commit':commit},
        'rd_values':values,'unique_stored_field_lemmas':fields,'target_aliases_state_word_0':True,
        'preserved_native_projection_cells':sorted(protected),'export_replay':replay,
        'external_premises':certificate['external_premises'],'new_environmental_premises':[]}


def local_proof(component,audit,values,out,yosys,*,relax=None):
    out.mkdir();(out/'harness.sv').write_text(harness(component,audit,values,relax=relax))
    path=out.parent/'component.json';model=out/'model.smt2'
    script=f'read_json {yosys_path(path)}\nsetundef -anyseq\nbwmuxmap\nbmuxmap\ndemuxmap\nsetundef -anyseq\n'
    script+=f'read_verilog -formal -sv {yosys_path(out/"harness.sv")}\n'+formal_prepare_command('RegisterStatusProof')
    script+=formal_lower_command(yosys)+'async2sync\ndffunmap\nsetundef -anyseq\ncheck -assert\n'
    script+=f'write_json {yosys_path(out/"lowered.json")}\nwrite_smt2 -wires {yosys_path(model)}\n'
    export=checked_yosys(yosys,script,out,'export',30)
    lowered=read(out/'lowered.json');clock=validate_single_clock(lowered,'RegisterStatusProof')
    m=lowered['modules']['RegisterStatusProof'];counts={k:sum(c['type']=='$'+k for c in m['cells'].values()) for k in ('assert','assume','cover')}
    require(counts=={'assert':50,'assume':3 if relax is None else 2,'cover':0},'Local proof property inventory changed')
    require(not any(b in ('x','z') for c in m['cells'].values() for bs in c['connections'].values() for b in bs),'Undefined literal survived safe preparation')
    args=[str(Path(yosys).with_name('yosys-smtbmc')),'-s','z3','-t','4','--noprogress']
    base=run_command(args+['--dump-vcd',str(out/'counterexample.vcd'),str(model)],out/'base.log',30)
    record={'status':'unproved','relaxed_index_domain':relax,'export':export,'base':base,
        'clock_model':clock,'property_counts':counts,'harness_sha256':digest(out/'harness.sv'),
        'model_sha256':digest(model),'lowered_sha256':digest(out/'lowered.json')}
    if relax is None:
        require(proof_passed(base),'Native local reset base failed')
        induction=run_command(args+['-i',str(model)],out/'induction.log',30)
        require(proof_passed(induction) and 'Temporal induction successful.' in (out/'induction.log').read_text(),'Native local reset induction failed')
        record.update(status='proved_unbounded',induction=induction)
    else:
        log=(out/'base.log').read_text()
        require(base['returncode']==1 and not base['timeout'] and 'Status: FAILED' in log
            and 'Assert failed' in log and (out/'counterexample.vcd').exists() and 'ERROR' not in log,'Negative control did not yield a real counterexample')
        record.update(status='counterexample',counterexample_sha256=digest(out/'counterexample.vcd'))
    (out/'summary.json').write_text(json.dumps(record,indent=2)+'\n');return record


def reset_substitution(design,audit):
    result=copy.deepcopy(design);m=result['modules']['datapath'];changes={};deleted=[]
    for entry in audit['unused_entries']:
        for field in entry['fields']:
            name=field['native_cell'];cell=m['cells'][name]
            require(cell['type']=='$aldff' and cell['connections']['Q']==field['q_bits']
                and cell['connections']['AD']==field['reset_bits'],'Reset-state source binding changed')
            for bit in field['q_bits']:
                require(bit not in changes,'Overlapping state rewrite');changes[bit]='0'
            del m['cells'][name];deleted.append(name)
    require(not set(changes)&{b for p in m['ports'].values() if p['direction']=='input' for b in p['bits']},'Cannot replace a native input')
    for cell in m['cells'].values():
        for pin,bits in cell['connections'].items():cell['connections'][pin]=[changes.get(b,b) for b in bits]
    for collection in ('ports','netnames'):
        for net in m[collection].values():net['bits']=[changes.get(b,b) for b in net['bits']]
    return result,{'constant_substitutions':changes,'deleted_ff_cells':deleted,'native_reset_bits':len(changes)}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('certificate','rd-domain','original-rf','prepared-rf','pair-recheck','lowering-proof','output'):
        parser.add_argument('--'+name,type=Path,required=True)
    parser.add_argument('--yosys',required=True)
    args=parser.parse_args();out=args.output.resolve();out.mkdir(parents=True,exist_ok=False)
    certificate=read(args.certificate);parent=read(Path(certificate['decoder_certificate']))
    directories=[args.rd_domain,args.original_rf.parent,args.prepared_rf,args.pair_recheck,args.lowering_proof,
        Path(certificate['native_candidate_json']).parent,Path(parent['native_original_json']).parent,
        Path(parent['native_candidate_json']).parent,Path(parent['domain_summary']).parent,Path(parent['paired_proof_summary']).parent]
    paths={p.resolve() for d in directories for p in d.rglob('*') if p.is_file()}
    paths.update(p.resolve() for p in ISA.glob('*.py'))
    paths.update((args.certificate.resolve(),Path(certificate['decoder_certificate']).resolve(),Path(__file__).resolve(),
        Path(replay_domain_export.__code__.co_filename).resolve(),Path(formal_prepare_command.__code__.co_filename).resolve()))
    dependencies={str(path):digest(path) for path in paths}
    original,candidate,chain=replay_rd_chain(args.certificate.resolve(),args.rd_domain.resolve(),args.original_rf.resolve(),args.prepared_rf.resolve(),
        args.pair_recheck.resolve(),args.lowering_proof.resolve(),out,args.yosys)
    component,audit=native_component(original,chain['rd_values'])
    require(all(original['modules']['datapath']['cells'][n]==candidate['modules']['datapath']['cells'][n]
        for n in audit['native_component_cells']),'Cumulative RF changes register-status logic')
    require(audit['reset_bits']==275 and len(audit['unused_entries'])==25,'Unexpected reset-state candidate inventory')
    (out/'component.json').write_text(json.dumps(component)+'\n')
    native_path=Path(certificate['native_candidate_json']);(out/'native_input.json').write_bytes(native_path.read_bytes())
    proofs={}
    for label,relax in (('positive',None),('negative_issue','issue'),('negative_commit','commit')):
        proofs[label]=local_proof(component,audit,chain['rd_values'],out/label,args.yosys,relax=relax)
        print(json.dumps({'case':label,'status':proofs[label]['status']}),flush=True)
    query,patch=reset_substitution(candidate,audit)
    (out/'query_only.json').write_text(json.dumps(query)+'\n')
    require(digest(out/'native_input.json')==certificate['native_candidate_sha256'],'Native export changed')
    check_dependencies(dependencies)
    record={'status':'program_only_register_status_reset_facts_composed','query_only':True,'accepted_optimization':False,
        'native_hardware_export_unchanged':True,'native_input_sha256':digest(out/'native_input.json'),
        'query_model_sha256':digest(out/'query_only.json'),'rd_theorem_chain':chain,'native_component_audit':audit,
        'local_proofs':proofs,'reset_substitution':patch,'new_environmental_premises':[],'timing_premises':[],
        'source_dependencies_sha256':dependencies,'external_premises':chain['external_premises'],
        'scope':'Only query-model reset constants under the closed original destination-field domain. No hardware/map/area claim. '
            'The two local index premises are exact existing native RD-theorem conclusions; all other interface inputs remain arbitrary.',
        'future_rd_import':'All40 distinct native stored destination fields already have unconditional proved membership assertions. '
            'Fresh encoding can strengthen ROB/issue proof queries without new premises; the duplicate target aliases field0. '
            'No such additional lemma cells are emitted in this run.'}
    (out/'register_status_lemmas_source.py').write_bytes(Path(__file__).read_bytes())
    (out/'summary.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({'status':record['status'],'reset_bits':patch['native_reset_bits']}))


if __name__=='__main__':main()
