#!/usr/bin/env python3
"""Discharge native MUL/DIV row reset theorems and emit a query-only model."""
import argparse
import copy
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE.parents[3]),str(HERE)]
from odc.temporal import checked_yosys,digest,formal_lower_command,formal_prepare_command,proof_passed,yosys_path
from eu_register_lemma import (dispatch_projection,native_path,proof_harness,read,
    register_projection,require,verify_decoder_dependency)
from reset_storage import conditional_rewrite,driver_map,project_row,prove_local,slice_reset_ff

BANKS={
    'mul':'u_backend.u_exec_stage.gen_mult_unit.u_mult_unit.gen_parallel_mult_unit.u_mult_rs.',
    'div':'u_backend.u_exec_stage.gen_div_unit.u_div_unit.u_div_rs.',
}


def validate_clock_reset(module,path):
    ff=path['ireg_assigned_eu_ff']['cell'];con=ff['connections'];par=ff['parameters']
    from odc.temporal import parameter_int
    require(module['ports']['clk_i']=={'direction':'input','bits':con['CLK']} and
            module['ports']['rst_ni']=={'direction':'input','bits':con['ALOAD']},
            'Native EU clock/reset do not match external proof premises')
    require(parameter_int(par['CLK_POLARITY'])==1 and parameter_int(par['ALOAD_POLARITY'])==0,
            'Native EU clock/reset polarity changed')


def insertion_binding(module,prefix,proved_valid):
    nets=module['netnames'];drivers=driver_map(module)
    valid=nets[prefix+'issue_valid_i']['bits'];ready=nets[prefix+'issue_ready_o']['bits'];insert=nets[prefix+'insert']['bits']
    require(valid==[proved_valid] and len(ready)==len(insert)==1,'FU insertion aliases differ from proved dispatch bits')
    name,pin,index=drivers[insert[0]];cell=module['cells'][name]
    require(pin=='Y' and index==0 and cell['type']=='$and' and cell['connections']=={'A':valid,'B':ready,'Y':insert},'Native insertion is not the exact proved-valid AND ready gate')
    require(all(int(cell['parameters'][p],2)==1 if isinstance(cell['parameters'][p],str) else cell['parameters'][p]==1
                for p in ('A_WIDTH','B_WIDTH','Y_WIDTH')),'Insertion gate is not one bit')
    return {'cell_name':name,'cell':copy.deepcopy(cell),'proved_issue_valid_bit':proved_valid,
        'arbitrary_ready_bit':ready[0],'native_insert_bit':insert[0],
        'discharge':'Native one-bit AND has a proved-zero input, so insert=0 for both possible ready values; therefore every reset-qualified no-admission row premise holds.'}


def replay_lowering(directory,output,yosys,*,sequential,diagnostic=False):
    """Replay only a whitelisted tiny model export; do not rerun the solver."""
    output.mkdir();script_name='export.ys' if sequential else 'check.ys'
    old=(directory/script_name).read_text()
    if diagnostic:
        expected=f'read_json {yosys_path(directory/"decoder.json")}\nsetundef -anyseq\n'
        expected+=f'write_json {yosys_path(directory/"symbolized_before_prep.json")}\nread_verilog -formal -sv {yosys_path(directory/"harness.sv")}\n'
        expected+=formal_prepare_command('EUDomainProof')+formal_lower_command(yosys)+'setundef -anyseq\n'
    else:
        expected=f'read_json {yosys_path(directory/"native.json")}\nsetundef -anyseq\nbwmuxmap\nbmuxmap\ndemuxmap\nsetundef -anyseq\n'
        expected+=f'read_verilog -formal -sv {yosys_path(directory/"harness.sv")}\n'+formal_prepare_command('EUProof')+formal_lower_command(yosys)
        if sequential:expected+='async2sync\ndffunmap\n'
        expected+='setundef -anyseq\ncheck -assert\n'
    expected+=f'write_json {yosys_path(directory/"lowered.json")}\n'
    if sequential:expected+=f'write_smt2 -wires {yosys_path(directory/"model.smt2")}\n'
    else:
        show='instruction_i -show assigned_eu' if diagnostic else 'registered_eu -show mul_valid -show div_valid'
        expected+=f'tee -o {yosys_path(directory/"sat.log")} sat -set-assumes -prove-asserts -show {show} -dump_vcd {yosys_path(directory/"counterexample.vcd")}\n'
    require(old==expected,'Stored proof export commands changed')
    fresh='\n'.join(line for line in old.splitlines() if not line.startswith('tee '))+'\n'
    for name in ('lowered.json','model.smt2','symbolized_before_prep.json'):
        fresh=fresh.replace(f'write_json {yosys_path(directory/name)}',f'write_json {yosys_path(output/name)}')
        fresh=fresh.replace(f'write_smt2 -wires {yosys_path(directory/name)}',f'write_smt2 -wires {yosys_path(output/name)}')
    execution=checked_yosys(yosys,fresh,output,'replay',20)
    require(read(directory/'lowered.json')==read(output/'lowered.json'),'Regenerated native lemma model differs')
    if sequential:require(digest(directory/'model.smt2')==digest(output/'model.smt2'),'Regenerated lemma SMT differs')
    if diagnostic:require(read(directory/'symbolized_before_prep.json')==read(output/'symbolized_before_prep.json'),'Preoptimization decoder symbolic model differs')
    return {'execution':execution,'old_lowered_sha256':digest(directory/'lowered.json'),'new_lowered_sha256':digest(output/'lowered.json'),
        'smt_sha256':digest(directory/'model.smt2') if sequential else None,'no_solver_query':True}


def validate_eu_chain(eu_run,certificate_path,diagnostic,out,yosys):
    eu=read(eu_run/'summary.json')
    require(eu['status']=='native_register_and_dispatch_lemmas_proved' and eu['new_environmental_premises']==[], 'Native dispatch chain is not proved')
    for path,sha in eu['dependency_sha256'].items():require(digest(Path(path))==sha,'EU proof dependency changed')
    original,candidate,certificate,replay=verify_decoder_dependency(certificate_path,diagnostic,HERE.parent/'isa_baseline/certify.py',out)
    path=native_path(original['modules']['datapath'])
    require(path==native_path(candidate['modules']['datapath']),'Certified decoder changed native issue-register/dispatch path')
    validate_clock_reset(original['modules']['datapath'],path)
    require(path['ireg_high_bit']==eu['native_visible_register_high_bit'] and path['mul_issue_valid_bit']==eu['native_mul_issue_valid_bit'] and
            path['div_issue_valid_bit']==eu['native_div_issue_valid_bit'],'EU proof native observations changed')
    require(register_projection(path)==read(eu_run/'register/native.json') and dispatch_projection(path)==read(eu_run/'dispatch/native.json'),'EU proof projections differ from original primitives')
    require((eu_run/'register/harness.sv').read_text()==proof_harness(register_projection(path),derived_premise=True,sequential=True),'Register proof premises changed')
    require((eu_run/'dispatch/harness.sv').read_text()==proof_harness(dispatch_projection(path),derived_premise=True,sequential=False),'Dispatch proof premises changed')
    reg,dispatch=eu['proofs']['register'],eu['proofs']['dispatch']
    require(reg['status']=='proved_unbounded' and proof_passed(reg['base']) and proof_passed(reg['induction']) and '-i' in reg['induction']['argv'],'Register lemma lacks induction')
    require(dispatch['status']=='proved_combinationally' and dispatch['execution']['returncode']==0 and not dispatch['execution']['timeout'],'Dispatch SAT failed')
    for name,result in [('register',reg),('dispatch',dispatch)]:
        require(digest(eu_run/name/'lowered.json')==result['lowered_json_sha256'] and digest(eu_run/name/'native.json')==result['native_json_sha256'] and
                digest(eu_run/name/'harness.sv')==result['harness_sha256'],'EU proof model/harness changed')
    for run in (reg['base'],reg['induction']):require(digest(Path(run['log']))==run['log_sha256'],'EU induction log changed')
    require(digest(eu_run/'register/model.smt2')==reg['smt_sha256'] and digest(eu_run/'dispatch/sat.log')==dispatch['sat_log_sha256'],'EU proof log/model changed')
    sat_text=(eu_run/'dispatch/sat.log').read_text()
    require(sat_text.count('SAT proof finished - no model found: SUCCESS!')==1 and
            'SAT proof finished - model found: FAIL!' not in sat_text and 'ERROR' not in sat_text,
            'Contradictory or unsuccessful dispatch SAT log')
    exports={'register':replay_lowering(eu_run/'register',out/'register_replay',yosys,sequential=True),
        'dispatch':replay_lowering(eu_run/'dispatch',out/'dispatch_replay',yosys,sequential=False),
        'decoder':replay_lowering(diagnostic/'candidate_unrestricted',out/'decoder_replay',yosys,sequential=False,diagnostic=True)}
    return original,candidate,certificate,eu,{'closed_certificate_replay':replay,'model_replays':exports}


def substitute_visible_register_high(design,path):
    result=copy.deepcopy(design);m=result['modules']['datapath'];item=path['ireg_assigned_eu_ff'];high=path['ireg_high_bit']
    require(m['cells'][item['name']]==item['cell'],'Native issue register changed before query substitution')
    require(high not in {bit for p in m['ports'].values() if p['direction']=='input' for bit in p['bits']},
            'Cannot substitute a hardware input driver')
    require(not any('init'in n.get('attributes',{}) and high in n['bits'] for n in m['netnames'].values()),'Explicit initialization on selected native alias unsupported')
    m['cells'][item['name']],_=slice_reset_ff(item['cell'],[0,1])
    for c in m['cells'].values():
        for pin,direction in c['port_directions'].items():
            if direction=='input':c['connections'][pin]=['0' if bit==high else bit for bit in c['connections'][pin]]
            else:require(high not in c['connections'][pin],'Selected visible high bit retains an output driver')
    for collection in (m['ports'],m['netnames']):
        for n in collection.values():n['bits']=['0' if bit==high else bit for bit in n['bits']]
    return result


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--eu-run',type=Path,required=True);p.add_argument('--certificate',type=Path,required=True)
    p.add_argument('--diagnostic',type=Path,required=True);p.add_argument('--rs-source',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True);p.add_argument('--yosys',required=True)
    args=p.parse_args();out=args.output.resolve();out.mkdir(parents=True,exist_ok=False)
    inputs=[args.eu_run.resolve()/'summary.json',args.certificate.resolve(),args.diagnostic.resolve()/'summary.json',args.rs_source.resolve(),
            Path(__file__),HERE/'reset_storage.py',HERE/'eu_register_lemma.py',HERE/'eu_domain_diagnostic.py']
    starting={str(path):digest(path) for path in inputs}
    original,candidate,certificate,eu,chain=validate_eu_chain(args.eu_run.resolve(),args.certificate.resolve(),args.diagnostic.resolve(),out,args.yosys)
    native_source=Path(certificate['native_candidate_json']);native_hash=digest(native_source)
    (out/'native_input.json').write_bytes(native_source.read_bytes())
    header=args.rs_source.read_text();records=[];banks={}
    for bank,prefix in BANKS.items():
        valid=eu['native_'+bank+'_issue_valid_bit'];binding=insertion_binding(original['modules']['datapath'],prefix,valid)
        require(candidate['modules']['datapath']['cells'][binding['cell_name']]==binding['cell'],'Certified candidate altered native insertion gate')
        module=original['modules']['datapath']
        require(module['netnames'][prefix+'clk_i']['bits']==module['ports']['clk_i']['bits'] and
                module['netnames'][prefix+'rst_ni']['bits']==module['ports']['rst_ni']['bits'],
                'Bank clock/reset differs from external initial-reset domain')
        depth=len(module['netnames'][prefix+'empty']['bits']);bankrows=[]
        for row in range(depth):
            projection,audit=project_row(original,row,header,prefix=prefix)
            required=set(audit['combinational_cells'])|{item['cell'] for item in audit['selected_ff_slices']}
            require(all(original['modules']['datapath']['cells'][name]==candidate['modules']['datapath']['cells'][name] for name in required),'Decoder substitution changed a bank proof cell')
            record=prove_local(projection,audit,out/f'{bank}_row_{row}',yosys=args.yosys,smtbmc=str(Path(args.yosys).with_name('yosys-smtbmc')),timeout=20)
            require(record['status']=='conditional_reset_storage_proved' and record['admission_during_reset_restricted'] is False,'Bank row reset theorem failed')
            records.append(record);bankrows.append({'row':row,'reset_ff_bits':audit['ff_bits'],'local_summary_sha256':digest(out/f'{bank}_row_{row}'/'summary.json')})
            print(json.dumps({'bank':bank,'row':row,'status':record['status'],'reset_ff_bits':audit['ff_bits']}),flush=True)
        banks[bank]={'prefix':prefix,'depth':depth,'insertion_discharge':binding,'rows':bankrows}
    rewritten,patch=conditional_rewrite(original,records)
    # Apply only the already-certified decoder changes to the same original
    # graph. They must not reintroduce any substituted native state bit.
    replaced={int(x) for x in patch['constant_substitutions']}
    a,b=original['modules']['datapath'],candidate['modules']['datapath']
    changed={name for name in a['cells'] if a['cells'][name]!=b['cells'][name]}
    require(changed==set(certificate['changed_cells']),'Unexpected candidate changes')
    for name in changed:
        require(not any(set(bs)&replaced for bs in b['cells'][name]['connections'].values()),'Decoder replacement overlaps row state')
        rewritten['modules']['datapath']['cells'][name]=copy.deepcopy(b['cells'][name])
    query=substitute_visible_register_high(rewritten,native_path(original['modules']['datapath']))
    require(not any(c['type'] in ('$assume','$assert','$check','$cover','$anyseq','$anyconst') for c in query['modules']['datapath']['cells'].values()),'Query substitution introduced formal hardware')
    (out/'query_only.json').write_text(json.dumps(query)+'\n')
    require(digest(native_source)==native_hash==digest(out/'native_input.json'),'Native input export changed')
    require(all(digest(Path(path))==sha for path,sha in starting.items()),'Source dependency changed during run')
    record={'status':'program_only_native_reset_facts_composed','query_only':True,'accepted_hardware_optimization':False,
        'native_hardware_export_unchanged':True,'native_input_sha256':native_hash,'native_input_path':str(native_source),
        'original_native_sha256':certificate['native_original_sha256'],'query_model_sha256':digest(out/'query_only.json'),
        'external_premises':certificate['external_premises'],'new_environmental_premises':[],'timing_premises':[],
        'eu_lemma_chain':chain,'banks':banks,'row_reset_substitution':patch,
        'discharged_prefix_rows':[{'prefix':r['projection']['prefix'],'row':r['projection']['row']} for r in records],
        'native_visible_register_high_substituted':eu['native_visible_register_high_bit'],
        'total_proved_reset_state_bits_substituted':patch['reset_constant_bits']+1,
        'source_dependency_sha256':starting,
        'composition':'Program-word decoder/visible-register/dispatch lemmas prove each native MUL/DIV issue-valid zero. Exact native one-bit insertion ANDs discharge every local row no-admission premise. Original row FF/reset projections prove each Q equals its source reset constant. Replacing these proven pointwise values at every consumer/alias and removing their FF slices preserves all outside behavior under the same initial-reset/program domain. The one native visible EU-register high bit is substituted by its own proved theorem. This is a separate proof model, with no added assumptions, capacity changes, physical mapping, or accepted hardware rewrite.'}
    (out/'inactive_fu_lemmas_source.py').write_bytes(Path(__file__).read_bytes())
    (out/'summary.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({'status':record['status'],'substituted_bits':record['total_proved_reset_state_bits_substituted']}))


if __name__=='__main__':main()
