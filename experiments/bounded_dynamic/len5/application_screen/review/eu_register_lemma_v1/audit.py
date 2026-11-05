#!/usr/bin/env python3
"""Independent read-only structural/provenance review; no solver calls."""
import copy
import hashlib
import itertools
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
APP=HERE.parents[1]
EVIDENCE=APP/'evidence/eu_register_lemma_v1'
def read(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    report=read(EVIDENCE/'summary.json');manifest=read(EVIDENCE/'manifest.json')
    certificate=read(EVIDENCE/'replayed_decoder_certificate.json')
    original_path=Path(certificate['native_original_json']);candidate_path=Path(certificate['native_candidate_json'])
    assert sha(original_path)==certificate['native_original_sha256']
    assert sha(candidate_path)==certificate['native_candidate_sha256']
    original=read(original_path)['modules']['datapath'];candidate=read(candidate_path)['modules']['datapath']
    dependencies=dict(report['dependency_sha256'])
    for path,expected in dependencies.items():assert sha(path)==expected,path
    for item in manifest['files']:
        assert sha(EVIDENCE/item['copy'])==sha(item['source'])==item['sha256'],item['copy']
        dependencies[str((EVIDENCE/item['copy']).resolve())]=item['sha256']
    drivers={}
    for name,cell in original['cells'].items():
        for pin,direction in cell['port_directions'].items():
            if direction=='output':
                for index,bit in enumerate(cell['connections'][pin]):
                    if type(bit)is int:drivers.setdefault(bit,[]).append((name,pin,index))
    native=read(EVIDENCE/'register/native.json')['modules']['NativeEURegister']
    q=native['ports']['visible_high']['bits'];assert q==[91687]
    ffname='$driver$u_backend.u_issue_stage.ireg_data_out.assigned_eu'
    assert drivers[91687]==[(ffname,'Q',2)]
    ff=copy.deepcopy(original['cells'][ffname]);assert ff==candidate['cells'][ffname]
    for pin in ('AD','D','Q'):ff['connections'][pin]=[ff['connections'][pin][2]]
    ff['parameters']['WIDTH']='00000000000000000000000000000001'
    assert ff==native['cells'][ffname]
    assert ff['connections']['AD']==['0'] and ff['connections']['CLK']==original['ports']['clk_i']['bits']==[2]
    assert ff['connections']['ALOAD']==original['ports']['rst_ni']['bits']==[3]
    assert int(ff['parameters']['ALOAD_POLARITY'],2)==0 and int(ff['parameters']['CLK_POLARITY'],2)==1
    for name,cell in native['cells'].items():
        if name==ffname:continue
        assert cell['type']=='$mux' and len(cell['connections']['Y'])==1
        target=cell['connections']['Y'][0]
        assert len(drivers[target])==1
        n,pin,index=drivers[target][0];assert n==name and pin=='Y'
        source=copy.deepcopy(original['cells'][name]);assert source==candidate['cells'][name]
        source['parameters']['WIDTH']='00000000000000000000000000000001'
        for port in ('A','B','Y'):source['connections'][port]=[source['connections'][port][index]]
        assert source==cell
    assert native['ports']['controls']['bits']==[91511,91658]
    assert native['ports']['decoded_high']['bits']==[202160]
    assert native['cells']['$procmux$39604']['connections']['S']==native['cells']['$procmux$39608']['connections']['S']==[91658]
    muxes={cell['connections']['Y'][0]:cell['connections'] for cell in native['cells'].values() if cell['type']=='$mux'}
    for old,decoded,enable,flush,x in itertools.product(range(2),repeat=5):
        env={91687:old,202160:decoded,91511:enable,91658:flush}
        def value(bit):
            if bit=='x':return x
            if isinstance(bit,str):return int(bit)
            if bit in env:return env[bit]
            c=muxes[bit];return value(c['B'][0] if value(c['S'][0]) else c['A'][0])
        assert value(139306)==(0 if flush else decoded if enable else old)
    dispatch=read(EVIDENCE/'dispatch/native.json')['modules']['NativeEUDispatch']
    assert all(cell==original['cells'][name]==candidate['cells'][name] for name,cell in dispatch['cells'].items())
    assert dispatch['ports']['registered_eu']['bits']==[91685,91686,91687]
    assert dispatch['ports']['mul_valid']['bits']==[67868] and dispatch['ports']['div_valid']['bits']==[71113]
    assert original['netnames']['u_backend.u_exec_stage.gen_mult_unit.u_mult_unit.issue_valid_i']['bits']==[67868]
    assert original['netnames']['u_backend.u_exec_stage.gen_div_unit.u_div_unit.issue_valid_i']['bits']==[71113]
    lowered=read(EVIDENCE/'register/lowered.json')['modules']['EUProof']
    observed=lowered['ports']['visible_high']['bits']
    output_drivers=[cell for cell in lowered['cells'].values() if any(bit in observed for pin,d in cell['port_directions'].items() if d=='output' for bit in cell['connections'][pin])]
    assert len(output_drivers)==1 and output_drivers[0]['type']=='$mux'
    assert output_drivers[0]['connections']['A']==['0'] and output_drivers[0]['connections']['S']==lowered['ports']['rst_ni']['bits']
    assert not any('init' in n.get('attributes',{}) for n in lowered['netnames'].values())
    for variant,expected in [('register',2),('register_negative',1),('dispatch',1),('dispatch_negative',0)]:
        p=report['proofs'][variant];m=read(EVIDENCE/variant/'lowered.json')['modules']['EUProof']
        assert p['property_counts']=={'assert':1,'assume':expected}
        assert not any(bit in ('x','z') for c in m['cells'].values() for bits in c['connections'].values() for bit in bits)
        assert sha(EVIDENCE/variant/'native.json')==p['native_json_sha256']
        assert sha(EVIDENCE/variant/'lowered.json')==p['lowered_json_sha256']
        assert sha(EVIDENCE/variant/'harness.sv')==p['harness_sha256']
        script=(EVIDENCE/variant/('export.ys' if variant.startswith('register') else 'check.ys')).read_text()
        assert script.index('setundef -anyseq')<script.index('bwmuxmap')<script.index('prep -top')
    assert 'Temporal induction successful.' in (EVIDENCE/'register/induction.log').read_text()
    assert (EVIDENCE/'register/base.log').read_text().count('Status: PASSED')==1
    assert (EVIDENCE/'dispatch/sat.log').read_text().count('SAT proof finished - no model found: SUCCESS!')==1
    diag=Path(next(name for name in report['dependency_sha256'] if name.endswith('eu_domain_diagnostic_v1/summary.json'))).parent
    d=read(diag/'summary.json');proof=d['tests']['candidate_unrestricted'];component=read(diag/'candidate_unrestricted/decoder.json')['modules']['DecoderBase']
    dm=read(diag/'candidate_unrestricted/lowered.json')['modules']['EUDomainProof']
    assert proof['domain_expression'] is None and dm['ports']['assigned_eu']['bits'][2]=='0'
    assert not any(c['type']=='$assume' for c in dm['cells'].values())
    assert all(cell==candidate['cells'][name] for name,cell in component['cells'].items())
    assert component['ports']['assigned_eu_o']['bits']==candidate['netnames']['u_backend.u_issue_stage.id_assigned_eu']['bits']==[202158,202159,202160]
    for filename,key in [('decoder.json','input_json_sha256'),('lowered.json','lowered_json_sha256'),('sat.log','proof_log_sha256')]:
        path=diag/'candidate_unrestricted'/filename;assert sha(path)==proof[key]
        dependencies[str(path)]=sha(path)
    for path,expected in dependencies.items():assert sha(path)==expected,path
    result={'status':'independent_source_and_composition_review_passed','new_solver_queries':0,
        'accepted_optimization':False,'review_source_sha256':sha(Path(__file__)),'dependency_sha256':dependencies,
        'native_visible_high_bit':91687,'native_decoder_high_bit':202160,
        'mul_issue_valid_bit':67868,'div_issue_valid_bit':71113,
        'native_register_data_equation':'flush ? 0 : (enable ? decoded_high : visible_high)',
        'shared_flush_bit':91658,'arbitrary_enable_bit':91511,'masked_x_independent':True,
        'native_visible_observation_not_internal_async2sync_q':True,
        'lowered_observation_driver':output_drivers[0],
        'external_premises':certificate['external_premises'],'new_environmental_premises':[],
        'local_derived_premises':['decoded_high == 0','registered_eu[2] == 0'],
        'proof_chain':'Closed program-domain decoder correspondence; unconditional certified-candidate high-bit zero; native visible register base+induction under initial reset and arbitrary shared controls; exact native demux/valid AND proves MUL/DIV issue valid zero.',
        'negative_controls':{'register':'Without decoded-high premise, visible_high becomes1 at SMT step2 after reset release',
            'dispatch':'Without registered-high premise, selector100 allows mul_valid1'},
        'limits':['Does not prove idle raw execution outputs or reset values of every RS/FU state bit.',
            'Does not justify replacing arbitrary async2sync internal FF-Q bits by zero.',
            'This is a conditional program-only theorem; exact Harvard applicability uses the separately proved external ROM domain.',
            'Further reset/output closure is required before removing FU storage or reporting area savings.']}
    (HERE/'summary.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({key:result[key] for key in ('status','native_visible_high_bit','masked_x_independent','new_environmental_premises')}))

if __name__=='__main__':main()
