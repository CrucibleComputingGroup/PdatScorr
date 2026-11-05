#!/usr/bin/env python3
"""Read-only structural/hash audit of the revalidated decoder transfer evidence."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import re


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def check_run(record, expected):
    assert record['returncode']==0 and not record['timeout']
    p=Path(record['log']);assert sha(p)==record['log_sha256']
    text=p.read_text()
    assert expected in text and not re.search(r'\b(ERROR|FAILED|UNDECIDED|was asserted)\b',text)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();b=args.build.resolve()
    prepared=b/'isa_baseline_prepare_v1';manifest=read(prepared/'manifest.json')
    original_path=prepared/'whole_core.json'
    assert sha(original_path)==manifest['whole_core_json_sha256']
    original=read(original_path)['modules']['datapath']
    decoder=read(prepared/'decoder.json')['modules']['DecoderBase']
    expected_outputs={'issue_type_o':4,'except_code_o':5,'assigned_eu_o':3,'skip_eu_o':1,
        'eu_ctl_o':4,'mem_crit_o':1,'order_crit_o':1,'rs1_req_o':1,'rs1_is_pc_o':1,
        'rs2_req_o':1,'rs2_is_imm_o':1,'rd_upd_o':1,'imm_format_o':3}
    assert {n:len(p['bits']) for n,p in decoder['ports'].items() if p['direction']=='output'}==expected_outputs
    assert {n for n,p in decoder['ports'].items() if p['direction']=='input'}=={'instruction_i'}
    component_bits={bit for c in decoder['cells'].values() for pin,direction in c['port_directions'].items()
                    if direction=='output' for bit in c['connections'][pin] if isinstance(bit,int)}
    observed={bit for p in decoder['ports'].values() if p['direction']=='output' for bit in p['bits']}
    outside_uses=[]
    for n,c in original['cells'].items():
        if n in decoder['cells']:
            assert c==decoder['cells'][n]
            continue
        for pin,direction in c['port_directions'].items():
            if direction=='input':
                for bit in set(c['connections'][pin])&component_bits:
                    assert bit in observed,(n,pin,bit)
                    outside_uses.append((n,pin,bit))
    for n,p in original['ports'].items():
        if p['direction']=='output':assert not (set(p['bits'])&component_bits-observed)
    result={'status':'passed','scope':'Independent decoder transfer audit; no new solver runs. The rd data projection is also checked, but RF substitution/fanout is outside this audit.',
        'original_sha256':sha(original_path),'decoder_outputs':expected_outputs,
        'decoder_output_bits':sum(expected_outputs.values()),'external_consuming_pin_bits':len(outside_uses),
        'unobserved_decoder_external_fanout':0,'domain_projections':{},'paired_decoder_proofs':{}}
    for name in ['isa_domain_symbolic_v4','alphabet_domain_symbolic_v4','rd_domain_symbolic_v5']:
        p=b/name;s=read(p/'summary.json');audit=s['projection'];m=read(p/'data_path.json')['modules']['InstructionDataPath']
        assert sha(original_path)==s['original_whole_core_sha256']
        assert sha(p/'prove_domain_source.py')==s['source_sha256'] and sha(p/'harness.sv')==s['harness_sha256']
        # Independently reconstruct each native primitive slice. No preparation
        # helper or certifier implementation is imported into this audit.
        for n,indices in audit['original_cell_slices'].items():
            cell=copy.deepcopy(original['cells'][n]);con=cell['connections'];typ=cell['type']
            if typ in ('$adff','$adffe','$aldff'):
                for pin in ('D','Q'):con[pin]=[con[pin][i] for i in indices]
                if typ=='$aldff':con['AD']=[con['AD'][i] for i in indices]
                else:cell['parameters']['ARST_VALUE']=''.join(cell['parameters']['ARST_VALUE'][::-1][i] for i in indices)[::-1]
            elif typ in ('$mux','$bwmux'):
                for pin in ['A','B','Y']+(['S'] if typ=='$bwmux' else []):con[pin]=[con[pin][i] for i in indices]
            elif typ=='$bmux':
                width=len(con['Y']);con['A']=[con['A'][j+i] for j in range(0,len(con['A']),width) for i in indices]
                con['Y']=[con['Y'][i] for i in indices]
            else:raise ValueError(typ)
            cell['parameters']['WIDTH']=format(len(indices),'032b')
            assert cell==m['cells'][n],n
        for n in audit['retained_spill_write_control_cells']:assert original['cells'][n]==m['cells'][n],n
        retained=set(audit['original_cell_slices'])|set(audit['retained_spill_write_control_cells'])
        assert set(m['cells'])==retained
        assert m['ports']['instruction_i']['bits']==original['ports']['instr_rdata_i']['bits']
        assert m['ports']['response_valid']['bits']==original['ports']['instr_rvalid_i']['bits']
        if name!='rd_domain_symbolic_v5':assert m['ports']['decoder_word']['bits']==decoder['ports']['instruction_i']['bits']
        snap=read(p/'symbolized_before_prep.json')['modules']['InstructionDataPath']
        assert sha(p/'symbolized_before_prep.json')==s['symbolized_before_prep_sha256']
        assert not any(x in ('x','z') for c in snap['cells'].values() for bs in c['connections'].values() for x in bs)
        count=sum(len(c['connections']['Y']) for c in snap['cells'].values() if c['type']=='$anyseq')
        assert count==s['symbolic_undefined_bits_before_prep']
        script=(p/'export.ys').read_text();assert script.index('setundef -anyseq')<script.index('prep -top')
        lower=read(p/'lowered.json')['modules']['DomainProof']
        assert not any(x in ('x','z') for c in lower['cells'].values() for bs in c['connections'].values() for x in bs)
        assert sum(c['type']=='$assume' for c in lower['cells'].values())==2
        assert s['status']=='proved';check_run(s['base'],'Status: PASSED');check_run(s['induction'],'Status: PASSED')
        result['domain_projections'][name]={'native_cells_exact':len(m['cells']),'state_fields':len(audit['state_words']),
            'field_widths':sorted({len(w['bits']) for w in audit['state_words']}),'symbolic_undefined_bits':count,
            'summary_sha256':sha(p/'summary.json'),'projection_sha256':sha(p/'data_path.json'),
            'base_log_sha256':s['base']['log_sha256'],'induction_log_sha256':s['induction']['log_sha256']}
    for label,candidate_name,domain_name in [('isa_pair_symbolic_v1','isa_operations_v2','isa_domain_symbolic_v4'),
                                           ('alphabet_pair_symbolic_v1','program_alphabet_v1','alphabet_domain_symbolic_v4')]:
        p=b/label;cdir=b/candidate_name;r=read(p/'summary.json');proof=r['proof'];candidate=read(cdir/'summary.json')
        assert r['status']=='proved' and proof['proven'];assert proof['property_counts']=={'assert':13,'assume':1,'cover':0}
        for key,ext in [('reference','v'),('candidate','v'),('harness','sv')]:assert sha(cdir/(key+'.'+ext))==proof[key+'_sha256']
        assert sha(p/'temporal_source.py')==proof['implementation_sha256']
        assert sha(p/'proof/miter.aig')==proof['aig_sha256'];check_run(proof['pdr'],'Property proved.')
        assert sha(cdir/'candidate_whole_core.json')==r['native_candidate_sha256']==candidate['candidate_whole_core_sha256']
        modified=read(cdir/'candidate_whole_core.json')['modules']['datapath']
        assert original['ports']==modified['ports'] and original['netnames']==modified['netnames']
        assert set(original['cells'])==set(modified['cells'])
        changed={n for n in original['cells'] if original['cells'][n]!=modified['cells'][n]}
        assert changed=={c['cell'] for c in candidate['accepted']} and changed<=set(decoder['cells'])
        domain=read(b/domain_name/'summary.json')['projection']
        assert not changed&(set(domain['original_cell_slices'])|set(domain['retained_spill_write_control_cells']))
        assert not any(c['type'] in ('$assume','$assert','$check','$cover','$anyseq','$anyconst') for c in modified['cells'].values())
        result['paired_decoder_proofs'][label]={'changed_cells':len(changed),'all_other_cells_and_ports_identical':True,
            'safe_preparation_source_sha256':proof['implementation_sha256'],'proof_summary_sha256':sha(p/'summary.json'),
            'candidate_native_sha256':r['native_candidate_sha256'],'pdr_log_sha256':proof['pdr']['log_sha256']}
    result['transfer_limit']='Requires native initial reset and response-valid instruction domain. Exact ROM/address/error behavior must separately imply that premise; no timing/occupancy assumption or savings claim is supplied by this audit.'
    result['review_source_sha256']=sha(Path(__file__))
    args.output.parent.mkdir(parents=True,exist_ok=True)
    assert not args.output.exists()
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'decoder_outputs':len(expected_outputs),'domain_projections':3}))


if __name__=='__main__':
    main()
