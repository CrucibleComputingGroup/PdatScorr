#!/usr/bin/env python3
"""Small source-bound EU selector diagnostic; no hardware rewrite acceptance."""
import argparse
import copy
import json
from pathlib import Path
import re
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[3]))
from odc.temporal import checked_yosys,digest,formal_lower_command,formal_prepare_command,yosys_path


def require(ok,message):
    if not ok:raise ValueError(message)


def sat_high_bit(design,expression,out,yosys):
    out.mkdir();native=out/'decoder.json';native.write_text(json.dumps(design)+'\n')
    harness=out/'harness.sv'
    lines=['module EUDomainProof(input [31:0] instruction_i, output [2:0] assigned_eu);',
           'DecoderBase dut(.instruction_i(instruction_i), .assigned_eu_o(assigned_eu));','always @* begin']
    if expression:lines.append('assume('+expression+');')
    lines+=['assert(assigned_eu[2] == 0);','end','endmodule','']
    harness.write_text('\n'.join(lines))
    script=f'read_json {yosys_path(native)}\nsetundef -anyseq\n'
    script+=f'write_json {yosys_path(out/"symbolized_before_prep.json")}\nread_verilog -formal -sv {yosys_path(harness)}\n'
    script+=formal_prepare_command('EUDomainProof')+formal_lower_command(yosys)+'setundef -anyseq\n'
    script+=f'write_json {yosys_path(out/"lowered.json")}\n'
    script+=f'tee -o {yosys_path(out/"sat.log")} sat -set-assumes -prove-asserts -show instruction_i -show assigned_eu -dump_vcd {yosys_path(out/"counterexample.vcd")}\n'
    execution=checked_yosys(yosys,script,out,'check',20)
    log=(out/'sat.log').read_text()
    success=log.count('SAT proof finished - no model found: SUCCESS!')
    failure=log.count('SAT proof finished - model found: FAIL!')
    require(success+failure==1 and 'ERROR' not in log,'Unknown SAT status')
    lower=json.loads((out/'lowered.json').read_text())['modules']['EUDomainProof']
    require(not any('ff' in c['type'].lower() or 'latch' in c['type'].lower() for c in lower['cells'].values()),'Diagnostic unexpectedly contains state')
    counts={k:sum(c['type']=='$'+k for c in lower['cells'].values()) for k in ('assert','assume')}
    require(counts=={'assert':1,'assume':1 if expression else 0},'Unexpected diagnostic premises/observations')
    return {'status':'proved_combinationally' if success else 'counterexample_found','execution':execution,
            'domain_expression':expression,'proof_log_sha256':digest(out/'sat.log'),
            'input_json_sha256':digest(native),'lowered_json_sha256':digest(out/'lowered.json'),
            'remaining_assigned_eu_port_bits':lower['ports']['assigned_eu']['bits'],
            'symbolic_undefined_input_bits_before_prep':sum(len(c['connections']['Y']) for c in
              json.loads((out/'symbolized_before_prep.json').read_text())['modules']['DecoderBase']['cells'].values() if c['type']=='$anyseq')}


def native_path(module):
    cells=module['cells'];drivers={bit:(name,pin,i) for name,c in cells.items() for pin,d in c['port_directions'].items()
        if d=='output' for i,bit in enumerate(c['connections'][pin]) if type(bit)is int}
    decoded=module['netnames']['u_backend.u_issue_stage.id_assigned_eu']['bits']
    ffname='$driver$u_backend.u_issue_stage.ireg_data_out.assigned_eu';ff=cells[ffname]
    require(len(decoded)==3 and ff['type']=='$aldff' and ff['connections']['AD']==['0']*3,'Unexpected native EU register')
    high=ff['connections']['Q'][2];slices={};cut={high,decoded[2]}
    def visit(bit):
        if type(bit)is not int or bit in cut:return
        name,pin,index=drivers[bit];c=cells[name]
        require(pin=='Y' and c['type']=='$mux','Unexpected high-bit pipeline primitive')
        s=copy.deepcopy(c);s['parameters']['WIDTH']='00000000000000000000000000000001'
        for p in ('A','B','Y'):s['connections'][p]=[c['connections'][p][index]]
        slices[name]=s
        visit(s['connections']['A'][0]);visit(s['connections']['B'][0])
    visit(ff['connections']['D'][2])
    controls=sorted({bit for c in slices.values() for bit in c['connections']['S'] if type(bit)is int})
    select_cells={name:copy.deepcopy(c) for name,c in cells.items() if c['type']=='$demux' and c['connections']['S']==ff['connections']['Q']}
    valid=module['netnames']['u_backend.u_exec_stage.issue_valid_i']['bits']
    dispatch={drivers[valid[i]][0]:copy.deepcopy(cells[drivers[valid[i]][0]]) for i in (4,5)}
    require(len(select_cells)==1 and len(dispatch)==1,'Unexpected native dispatch path')
    return {'decoder_assigned_eu_bits':decoded,'ireg_assigned_eu_ff':{'name':ffname,'cell':ff},
        'ireg_high_bit':high,'native_high_bit_data_mux_slices':slices,'arbitrary_control_cut_candidates':controls,
        'native_onehot_demux':select_cells,'native_dispatch_and':dispatch,'mul_issue_valid_bit':valid[4],'div_issue_valid_bit':valid[5],
        'register_packed_field_indices':[module['netnames']['u_backend.u_issue_stage.ireg_data_out']['bits'].index(bit) for bit in ff['connections']['Q']],
        'pipeline_theorem_status':'Not proved here. Candidate follow-up: decoder high bit zero -> native register high bit zero after reset, for arbitrary native enable/flush controls; then original onehot demux forces MUL/DIV issue valid zero.'}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--prepared',type=Path,required=True);p.add_argument('--candidate',type=Path,required=True)
    p.add_argument('--frontend',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--yosys',required=True);args=p.parse_args();out=args.output.resolve();out.mkdir(parents=True,exist_ok=False)
    manifest=json.loads((args.prepared/'manifest.json').read_text());native=args.prepared/'whole_core.json'
    require(digest(native)==manifest['whole_core_json_sha256'],'Original native source changed')
    require(digest(args.prepared/'decoder.json')==manifest['decoder_json_sha256'],'Original decoder changed')
    original=json.loads(native.read_text());decoder=json.loads((args.prepared/'decoder.json').read_text())
    candidate=json.loads((args.candidate/'candidate_whole_core.json').read_text());candidate_summary=json.loads((args.candidate/'summary.json').read_text())
    require(digest(args.candidate/'candidate_whole_core.json')==candidate_summary['candidate_whole_core_sha256'],'Candidate source changed')
    require(decoder['modules']['DecoderBase']['ports']['assigned_eu_o']['bits']==original['modules']['datapath']['netnames']['u_backend.u_issue_stage.id_assigned_eu']['bits'],'Decoder observation binding changed')
    modified=copy.deepcopy(decoder)
    for name in modified['modules']['DecoderBase']['cells']:
        require(decoder['modules']['DecoderBase']['cells'][name]==original['modules']['datapath']['cells'][name],'Component source differs')
        modified['modules']['DecoderBase']['cells'][name]=copy.deepcopy(candidate['modules']['datapath']['cells'][name])
    results={}
    for name,design,expression in [('original_alphabet',decoder,manifest['domains']['program_alphabet']['expression']),
                                    ('original_unrestricted',decoder,None),('candidate_unrestricted',modified,None)]:
        results[name]=sat_high_bit(design,expression,out/name,args.yosys)
    report={'accepted_optimization':False,'scope':'Combinational decoder theorem and source-path diagnostic only',
        'tests':results,'native_pipeline_path':native_path(original['modules']['datapath']),
        'source_sha256':{str(path.resolve()):digest(path) for path in [native,args.prepared/'decoder.json',args.prepared/'manifest.json',args.candidate/'candidate_whole_core.json',Path(__file__)]}}
    for name in ['rtl/expipe/issue-unit/issue_decoder.sv','rtl/expipe/issue-unit/issue_stage.sv','rtl/expipe/exec-units/exec_stage.sv','rtl/packages/expipe_pkg.sv']:
        source=args.frontend/'source'/name;report['source_sha256'][str(source.resolve())]=digest(source)
    (out/'eu_domain_diagnostic_source.py').write_bytes(Path(__file__).read_bytes())
    (out/'summary.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v['status'] for k,v in results.items()}))
    return 0 if results['original_alphabet']['status']=='proved_combinationally' else 1


if __name__=='__main__':raise SystemExit(main())
