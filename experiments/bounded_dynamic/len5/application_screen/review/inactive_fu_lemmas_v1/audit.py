#!/usr/bin/env python3
"""Independent inactive-FU composition audit; no generator rewrite or solver."""
import copy
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
APP=HERE.parents[1]
EVIDENCE=APP/'evidence/inactive_fu_lemmas_v1'
def read(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def integer(v):return int(v,2) if isinstance(v,str) else v

def drivers(module):
    found={}
    for name,cell in module['cells'].items():
        for pin,direction in cell['port_directions'].items():
            if direction=='output':
                for index,bit in enumerate(cell['connections'][pin]):
                    if type(bit)is int:
                        assert bit not in found,('multiple native driver',bit)
                        found[bit]=(name,pin,index)
    return found

def slice_aldff(cell,indices):
    result=copy.deepcopy(cell)
    assert cell['type']=='$aldff' and integer(cell['parameters']['CLK_POLARITY'])==1
    assert integer(cell['parameters']['ALOAD_POLARITY'])==0
    assert cell['connections']['CLK']==[2] and cell['connections']['ALOAD']==[3]
    assert all(x=='0' for x in cell['connections']['AD'])
    for pin in ('AD','D','Q'):result['connections'][pin]=[cell['connections'][pin][i] for i in indices]
    result['parameters']['WIDTH']=format(len(indices),'032b')
    return result

def vcd_rows(path):
    scopes=[];codes={};values={};rows=[];time=None;touched=False
    def save():
        if touched and 'smt_step'in values:rows.append({'time':time,**values})
    for line in path.read_text().splitlines():
        fields=line.split()
        if fields and fields[0]=='$scope':scopes.append(fields[2])
        elif fields and fields[0]=='$upscope':scopes.pop()
        elif fields and fields[0]=='$var':
            if fields[4]=='smt_step' or (len(scopes)==1 and fields[4] in ['row_q','insert_i','new_index_i','rst_ni']):
                codes[fields[3]]=fields[4]
        elif line.startswith('#'):
            save();time=int(line[1:]);touched=False
        elif line.startswith('b'):
            bits,code=line[1:].split()
            if code in codes:
                assert set(bits)<={'0','1'}
                values[codes[code]]=int(bits,2);touched|=codes[code]=='row_q'
    save();return rows

def main():
    summary=read(EVIDENCE/'summary.json');manifest=read(EVIDENCE/'manifest.json')
    raw=Path(manifest['source_run']);cert=read(EVIDENCE/'replayed_decoder_certificate.json')
    original_path=Path(cert['native_original_json']);candidate_path=Path(cert['native_candidate_json'])
    assert sha(original_path)==cert['native_original_sha256']==summary['original_native_sha256']
    assert sha(candidate_path)==cert['native_candidate_sha256']==summary['native_input_sha256']==sha(raw/'native_input.json')
    assert sha(raw/'query_only.json')==summary['query_model_sha256']
    dependencies={str(original_path):sha(original_path),str(candidate_path):sha(candidate_path),
        str(raw/'query_only.json'):sha(raw/'query_only.json'),str(Path(__file__).resolve()):sha(Path(__file__))}
    dependencies.update(summary['source_dependency_sha256'])
    previous=HERE.parent/'eu_register_lemma_v1/summary.json'
    prior=read(previous);assert prior['status']=='independent_source_and_composition_review_passed'
    dependencies[str(previous.resolve())]=sha(previous);dependencies.update(prior['dependency_sha256'])
    for item in manifest['files']:
        assert sha(EVIDENCE/item['copy'])==sha(item['source'])==item['sha256'],item['copy']
        dependencies[str((EVIDENCE/item['copy']).resolve())]=item['sha256']
    for item in manifest['omitted_external_files']:
        assert sha(item['source'])==item['sha256'],item['source']
        dependencies[item['source']]=item['sha256']
    original=read(original_path);candidate=read(candidate_path);query=read(raw/'query_only.json')
    a=original['modules']['datapath'];b=candidate['modules']['datapath'];native_drivers=drivers(a)
    header_path=Path(next(p for p in summary['source_dependency_sha256'] if p.endswith('/arith_rs.sv')))
    header=header_path.read_text();assert '[DEPTH-1:0] data' in header and '[DEPTH-1:0] curr_state' in header
    replacements={};selected={};row_checks=[]
    for bank,bank_info in summary['banks'].items():
        prefix=bank_info['prefix'];binding=bank_info['insertion_discharge']
        gate=a['cells'][binding['cell_name']];assert gate==binding['cell']==b['cells'][binding['cell_name']]
        valid=67868 if bank=='mul' else 71113
        assert binding['proved_issue_valid_bit']==valid
        assert gate['type']=='$and' and gate['connections']=={
            'A':[valid],'B':[binding['arbitrary_ready_bit']],'Y':[binding['native_insert_bit']]}
        assert all(integer(gate['parameters'][p])==1 for p in ['A_WIDTH','B_WIDTH','Y_WIDTH'])
        assert a['netnames'][prefix+'issue_valid_i']['bits']==[valid]
        assert a['netnames'][prefix+'insert']['bits']==[binding['native_insert_bit']]
        assert bank_info['depth']==len(a['netnames'][prefix+'empty']['bits'])==4
        assert [r['row'] for r in bank_info['rows']]==list(range(4))
        # Zero AND either possible ready discharges no-admission for every index.
        assert all((0 & ready)==0 for ready in (0,1))
        for entry in bank_info['rows']:
            index=entry['row'];name=f'{bank}_row_{index}';d=raw/name
            r=read(d/'summary.json');p=r['projection'];projected=read(d/'projection.json')['modules']['NativeRow']
            assert sha(d/'summary.json')==entry['local_summary_sha256']
            dependencies[str(d/'summary.json')]=sha(d/'summary.json');dependencies.update(r['dependencies_sha256'])
            assert p['prefix']==prefix and p['row']==index and p['depth']==4
            assert p['ff_bits']==220 and p['native_constant_alias_bits']==0
            expected_q=[]
            for field,width in [('data',217),('curr_state',3)]:
                packed=a['netnames'][prefix+field]['bits'];assert len(packed)==4*width
                bits=packed[index*width:(index+1)*width]
                assert p['fields'][field]=={'width':width,'bits':bits};expected_q+=bits
            assert p['row_bits']==expected_q==projected['ports']['row_q']['bits']
            assert p['reset_bits']==['0']*220 and len(set(expected_q))==220
            assert not set(expected_q)&set(replacements)
            ff_names={item['cell'] for item in p['selected_ff_slices']}
            assert set(projected['cells'])==ff_names|set(p['combinational_cells'])
            for item in p['selected_ff_slices']:
                cell=a['cells'][item['cell']];indices=item['indices']
                assert cell==b['cells'][item['cell']]
                assert projected['cells'][item['cell']]==slice_aldff(cell,indices)
                assert item['q_bits']==[cell['connections']['Q'][i] for i in indices]
                assert item['reset_bits']==['0']*len(indices)
                for i,bit in zip(indices,item['q_bits']):
                    assert native_drivers[bit]==(item['cell'],'Q',i)
                    replacements[bit]='0';selected.setdefault(item['cell'],set()).add(i)
            for cell_name in p['combinational_cells']:
                assert projected['cells'][cell_name]==a['cells'][cell_name]==b['cells'][cell_name]
                assert not any(t in projected['cells'][cell_name]['type'].lower() for t in ('ff','latch','mem','assume','assert','any'))
            for port,bits in p['source_input_ports'].items():assert a['netnames'][prefix+port]['bits']==bits
            assert projected['ports']['clk_i']['bits']==[2] and projected['ports']['rst_ni']['bits']==[3]
            assert projected['ports']['insert_i']['bits']==[binding['native_insert_bit']]
            assert projected['ports']['new_index_i']['bits']==a['netnames'][prefix+'new_idx']['bits']
            inputs=[bit for port in projected['ports'].values() if port['direction']=='input' for bit in port['bits']]
            pd=drivers(projected)
            assert len(inputs)==len(set(inputs)) and not set(inputs)&set(pd)
            assert not set(inputs)&set(expected_q)
            for cell in projected['cells'].values():
                assert all(type(bit)is not int or bit in set(inputs)|set(pd)
                    for pin,bits in cell['connections'].items() if cell['port_directions'][pin]=='input' for bit in bits)
            for bit in p['arbitrary_other_ff_q_bits']:
                fn,pin,_=native_drivers[bit];assert pin=='Q' and 'ff'in a['cells'][fn]['type'] and bit not in expected_q
            # Reconstruct exact local premise and observation; no hidden idle input.
            ports=projected['ports'];decl=[f'input [{len(port["bits"])-1}:0] {n}' for n,port in ports.items() if port['direction']=='input']
            lines=['module ResetStorageProof('+', '.join(decl)+');','wire [219:0] row_q;',
                'NativeRow dut('+', '.join(f'.{n}({n})' for n in ports)+');','always @* begin',
                '  if ($initstate) assume(!rst_ni);']
            premise=f"  if (rst_ni) assume(!(insert_i && new_index_i == 2'd{index}));"
            tail=["  assert(row_q == 220'b"+'0'*220+');','end','endmodule','']
            assert (d/'positive/harness.sv').read_text()=='\n'.join(lines+[premise]+tail)
            assert (d/'negative/harness.sv').read_text()=='\n'.join(lines+tail)
            for polarity,assumptions in [('positive',2),('negative',1)]:
                f=d/polarity;model=read(f/'lowered.json')['modules']['ResetStorageProof']
                assert sum(c['type']=='$assert' for c in model['cells'].values())==1
                assert sum(c['type']=='$assume' for c in model['cells'].values())==assumptions
                assert not any(c['type'] in ('$cover','$live','$fair') for c in model['cells'].values())
                assert not any(bit in ('x','z') for c in model['cells'].values() for bits in c['connections'].values() for bit in bits)
                assert not any('init'in net.get('attributes',{}) for net in model['netnames'].values())
                script=(f/'export.ys').read_text();assert script.index('setundef -anyseq')<script.index('bwmuxmap')<script.index('prep -top')
                if polarity=='positive':
                    ld=drivers(model)
                    for bit in model['netnames']['row_q']['bits']:
                        cn,pin,i=ld[bit];cell=model['cells'][cn]
                        assert cell['type']=='$mux' and pin=='Y' and cell['connections']['A'][i]=='0'
                        assert cell['connections']['S']==model['ports']['rst_ni']['bits']
            pos=r['proofs']['positive'];neg=r['proofs']['negative']
            assert r['status']=='conditional_reset_storage_proved' and not r['admission_during_reset_restricted']
            assert pos['proven'] and neg['counterexample_found']
            for mode in ('base','induction'):
                run=pos[mode];assert run['returncode']==0 and not run['timeout']
                assert run['argv'][-1]==str(d/'positive/model.smt2')
                assert ('-i'in run['argv'])==(mode=='induction')
                text=(d/'positive'/f'{mode}.log').read_text();assert text.count('Status: PASSED')==1
                if mode=='induction':assert 'Temporal induction successful.'in text
            frames=vcd_rows(d/'negative/counterexample.vcd')
            failures=[frame for frame in frames if frame['row_q']!=0]
            admissions=[frame for frame in frames if frame['rst_ni']==1 and frame['insert_i']==1 and frame['new_index_i']==index]
            assert failures and admissions
            row_checks.append({'bank':bank,'row':index,'native_bits':220,'state_cells':len(ff_names),
                'retained_combinational_cells':len(p['combinational_cells']),
                'arbitrary_other_state_bits':len(p['arbitrary_other_ff_q_bits']),
                'literal_x_occurrences_before_symbolization':sum(bit=='x' for c in projected['cells'].values() for bs in c['connections'].values() for bit in bs),
                'positive_assumptions':2,'negative_assumptions':1,'base_and_induction_passed':True,
                'first_negative_admission':admissions[0],'first_negative_failure':failures[0]})
    assert len(replacements)==1760 and replacements=={int(bit):value for bit,value in summary['row_reset_substitution']['constant_substitutions'].items()}
    high=summary['native_visible_register_high_substituted'];assert high==91687 and high not in replacements
    replacements[high]='0';selected['$driver$u_backend.u_issue_stage.ireg_data_out.assigned_eu']={2}
    # Independent complete graph reconstruction starts with the certified
    # candidate, rather than using either generator substitution function.
    expected=copy.deepcopy(candidate);m=expected['modules']['datapath'];deleted=[];sliced=[]
    for name,indices in selected.items():
        cell=m['cells'][name];keep=[i for i in range(len(cell['connections']['Q'])) if i not in indices]
        if keep:m['cells'][name]=slice_aldff(cell,keep);sliced.append(name)
        else:del m['cells'][name];deleted.append(name)
    for cell in m['cells'].values():
        for pin,direction in cell['port_directions'].items():
            if direction=='input':cell['connections'][pin]=[replacements.get(bit,bit) for bit in cell['connections'][pin]]
            else:assert not set(cell['connections'][pin])&set(replacements)
    for collection in (m['ports'],m['netnames']):
        for net in collection.values():net['bits']=[replacements.get(bit,bit) for bit in net['bits']]
    assert expected==query
    assert len(deleted)==80 and len(sliced)==1 and len(replacements)==1761
    assert not any(cell['type'] in ('$assume','$assert','$check','$cover','$anyseq','$anyconst') for cell in m['cells'].values())
    assert len(candidate['modules']['datapath']['cells'])-len(m['cells'])==80
    for name,net in b['netnames'].items():assert len(m['netnames'][name]['bits'])==len(net['bits'])
    for name,port in b['ports'].items():assert len(m['ports'][name]['bits'])==len(port['bits'])
    for path,expected_hash in dependencies.items():assert sha(path)==expected_hash,path
    result={'status':'independent_end_to_end_composition_review_passed','new_solver_queries':0,'no_commit_performed':True,
        'source_sha256':dependencies,'native_candidate_sha256':sha(candidate_path),'query_sha256':sha(raw/'query_only.json'),
        'previous_eu_review_sha256':sha(previous),'row_checks':row_checks,
        'row_bits_substituted':1760,'native_visible_eu_bits_substituted':1,'total_bits_substituted':1761,
        'exact_full_query_graph_reconstructed':True,'deleted_native_ff_cells':len(deleted),'sliced_native_ff_cells':sliced,
        'formal_cells_added':0,'all_other_graph_objects_preserved_except_proved_constant_fanout':True,
        'net_port_widths_and_capacity_parameters_preserved':True,'new_environmental_or_timing_premises':[],
        'verdict':'No blocker. The source-bound program-only EU chain proves native insert zero; all eight row no-admission premises are therefore discharged. Original visible reset-Q invariants justify exactly1760 row bits plus the one visible EU bit. Replacing those pointwise values at every original consumer/alias reproduces the query-only JSON exactly.',
        'scope_limits':['Conditional on the existing initial-reset/program-word-domain contract; Harvard applicability uses the separate ROM theorem.',
            'The local row summaries intentionally retain their conditional status; standalone local records do not discharge their own premises.',
            'No assumption is made about raw internal async2sync FF-Q bits, and no execution-unit arithmetic/result output is directly cut.',
            'This accepts a source-bound proof-model substitution only, not an area result, hardware release, or whole-core admission bound.']}
    (HERE/'summary.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({key:result[key] for key in ('status','row_bits_substituted','total_bits_substituted','exact_full_query_graph_reconstructed','deleted_native_ff_cells','formal_cells_added')}))

if __name__=='__main__':main()
