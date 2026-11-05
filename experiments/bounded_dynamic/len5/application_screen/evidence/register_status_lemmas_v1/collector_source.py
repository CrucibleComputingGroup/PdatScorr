#!/usr/bin/env python3
"""Audit and package existing native register-status local proofs; no solver."""
import argparse
import copy
import gzip
import json
from pathlib import Path

from register_status_lemmas import (check_dependencies,digest,harness,native_component,
    proof_passed,read,require,reset_substitution)


def vcd_samples(path):
    scope=[];names={};values={};rows=[];sampled=False
    for line in Path(path).read_text().splitlines():
        words=line.split()
        if not words:continue
        if words[0]=='$scope':scope.append(words[2])
        elif words[0]=='$upscope':scope.pop()
        elif words[0]=='$var':
            if scope==['RegisterStatusProof'] or words[4]=='smt_step':names[words[3]]=words[4]
        elif line.startswith('#'):
            if sampled:rows.append(dict(values))
            sampled=False
        elif line.startswith('b') and len(words)==2 and words[1] in names:
            name=names[words[1]];bits=words[0][1:]
            require(set(bits)<={'0','1'},'Counterexample has symbolic selected witness value')
            values[name]=int(bits,2)
            if name=='smt_step':sampled=True
        elif line[0] in '01' and line[1:] in names:
            values[names[line[1:]]]=int(line[0])
    if sampled:rows.append(dict(values))
    require(len({r['smt_step'] for r in rows})==len(rows),'Duplicate SMT samples')
    return rows


def negative_witness(path,kind,allowed):
    rows=vcd_samples(path)
    require(rows and rows[0]['smt_step']==0 and rows[0]['rst_ni']==0,'Counterexample lacks initial reset')
    for previous,current in zip(rows,rows[1:]):
        if current['smt_step']!=previous['smt_step']+1:continue
        index=previous['issue_rd_idx_i' if kind=='issue' else 'comm_rd_idx_i']
        signal=f'count_{index}'
        if index in allowed or signal not in current or current[signal]==0:continue
        require(previous['rst_ni']==current['rst_ni']==1 and previous['flush_i']==0,'Witness update was reset or flushed')
        require(previous['issue_valid_i' if kind=='issue' else 'comm_valid_i']==1,'Witness lacks actual update valid')
        require(previous[signal]==0 and current[signal]==(1 if kind=='issue' else 63),'Witness is not the actual zero-to-update transition')
        retained='comm_rd_idx_i' if kind=='issue' else 'issue_rd_idx_i'
        require(all(r[retained] in allowed for r in rows),'Retained index premise violated')
        return {'removed_domain':kind,'update_step':previous['smt_step'],'failure_step':current['smt_step'],
            'register':index,'old_count':previous[signal],'new_count':current[signal],
            'actual_valid_update_verified':True,'samples':rows}
    raise ValueError('No concrete excluded-register update found in negative witness')


def audit_run(run):
    result=read(run/'summary.json')
    require(result['status']=='program_only_register_status_reset_facts_composed' and result['accepted_optimization'] is False,
        'Unqualified local register-status result')
    check_dependencies(result['source_dependencies_sha256'])
    source=Path(__file__).with_name('register_status_lemmas.py')
    require(digest(source)==digest(run/'register_status_lemmas_source.py'),'Generator source changed')
    original=read(Path(next(p for p in result['source_dependencies_sha256'] if p.endswith('/isa_baseline_prepare_v1/whole_core.json'))))
    component,audit=native_component(original,result['rd_theorem_chain']['rd_values'])
    require(component==read(run/'component.json') and audit==result['native_component_audit'],'Local native component differs')
    native=read(run/'native_input.json');query=read(run/'query_only.json')
    require(digest(run/'native_input.json')==result['native_input_sha256'],'Native input changed')
    require(digest(run/'query_only.json')==result['query_model_sha256'],'Query model changed')
    require(all(original['modules']['datapath']['cells'][n]==native['modules']['datapath']['cells'][n]
        for n in audit['native_component_cells']),'Cumulative RF candidate changed the component')
    rebuilt,patch=reset_substitution(native,audit)
    require(query==rebuilt and result['reset_substitution']==json.loads(json.dumps(patch)),'Query is not the exact275-bit substitution')
    # Independent whole-graph audit, without relying on the generator rewrite.
    a,b=native['modules']['datapath'],query['modules']['datapath']
    replacements={int(k):v for k,v in result['reset_substitution']['constant_substitutions'].items()}
    deleted=set(result['reset_substitution']['deleted_ff_cells'])
    require(len(replacements)==275 and len(deleted)==50 and set(b['cells'])==set(a['cells'])-deleted,'Incorrect state-removal inventory')
    for name,cell in a['cells'].items():
        if name in deleted:
            require(cell['type']=='$aldff' and all(replacements.get(bit)==reset for bit,reset in zip(cell['connections']['Q'],cell['connections']['AD'])),
                'Removed state is not bound to its own reset values')
            continue
        expected=copy.deepcopy(cell)
        for pin,bits in expected['connections'].items():expected['connections'][pin]=[replacements.get(bit,bit) for bit in bits]
        require(expected==b['cells'][name],'Non-reset native function changed')
    for collection in ('ports','netnames'):
        expected=copy.deepcopy(a[collection])
        for net in expected.values():net['bits']=[replacements.get(bit,bit) for bit in net['bits']]
        require(expected==b[collection],'Native alias/port changed outside exact reset constants')
    proof_records={};witnesses={}
    for label,relax in (('positive',None),('negative_issue','issue'),('negative_commit','commit')):
        directory=run/label;record=result['local_proofs'][label]
        require(read(directory/'summary.json')==record,'Local proof record differs')
        require((directory/'harness.sv').read_text()==harness(component,audit,result['rd_theorem_chain']['rd_values'],relax=relax),
            'Local premises or assertions changed')
        require(digest(directory/'model.smt2')==record['model_sha256'] and digest(directory/'lowered.json')==record['lowered_sha256'],
            'Local formal model changed')
        for kind in ('base','induction'):
            if kind not in record:continue
            execution=record[kind]
            require(digest(Path(execution['log']))==execution['log_sha256'],'Local solver log changed')
            require(execution['argv'][-1]==str(directory/'model.smt2'),'Solver model binding differs')
        if relax is None:
            require(proof_passed(record['base']) and proof_passed(record['induction']) and '-i' in record['induction']['argv']
                and 'Temporal induction successful.' in (directory/'induction.log').read_text(),'Missing unbounded local proof')
        else:
            require(record['status']=='counterexample' and record['base']['returncode']==1 and not record['base']['timeout']
                and 'Assert failed' in (directory/'base.log').read_text(),'Missing negative proof failure')
            require(digest(directory/'counterexample.vcd')==record['counterexample_sha256'],'Negative trace changed')
            witnesses[label]=negative_witness(directory/'counterexample.vcd',relax,result['rd_theorem_chain']['rd_values'])
        proof_records[label]={'status':record['status'],'summary_sha256':digest(directory/'summary.json')}
    protected=result['rd_theorem_chain']['preserved_native_projection_cells']
    require(all(a['cells'][name]==b['cells'][name] for name in protected),'RD projection changed after reset substitution')
    return result,{'status':'exact_native_reset_substitution_audit_passed','native_cells':len(audit['native_component_cells']),
        'native_state_bits':audit['native_state_bits'],'proved_reset_bits':275,'removed_ff_cells':50,
        'rd_projection_cells_preserved':len(protected),'source_dependency_count':len(result['source_dependencies_sha256']),
        'local_proofs':proof_records,'negative_witnesses':witnesses,'accepted_optimization':False}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run',type=Path,required=True);parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();run=args.run.resolve();result,audit=audit_run(run)
    out=args.output.resolve();out.mkdir(parents=True,exist_ok=False);artifacts=[];external=[]
    def keep(path,relative):
        raw=path.read_bytes();compress=len(raw)>100000
        if compress:relative+='.gz'
        dest=out/relative;dest.parent.mkdir(parents=True,exist_ok=True)
        dest.write_bytes(gzip.compress(raw,mtime=0) if compress else raw)
        artifacts.append({'path':relative,'sha256':digest(dest),'source':str(path),'source_sha256':digest(path),'gzip':compress})
    for path in sorted(run.rglob('*')):
        if not path.is_file():continue
        if path.name in ('native_input.json','query_only.json'):
            external.append({'path':str(path),'sha256':digest(path),'bytes':path.stat().st_size});continue
        keep(path,'run/'+str(path.relative_to(run)))
    root=Path(__file__).resolve().parents[4]
    keep(root/'tests/unit/test_register_status_lemmas.py','test_register_status_lemmas.py')
    keep(Path(__file__),'collector_source.py')
    (out/'audit.json').write_text(json.dumps(audit,indent=2)+'\n')
    (out/'PROVENANCE.json').write_text(json.dumps({'status':result['status'],'accepted_optimization':False,
        'query_only':True,'native_hardware_unchanged':True,'new_environmental_premises':[],
        'proved_registers':[e['register'] for e in result['native_component_audit']['unused_entries']],
        'proved_counter_bits':150,'proved_last_writer_bits':125,'rd_field_lemmas_available':40,
        'graph_and_witness_audit':audit,'artifacts':artifacts,'external_large_models':external,
        'scope':'Closed program-only reset facts and exact query-only substitution. No full-core admission proof, timing-derived optimization, physical map, or area claim.'},indent=2)+'\n')
    (out/'SHA256SUMS').write_text(''.join(f'{digest(path)}  {path.relative_to(out)}\n' for path in sorted(out.rglob('*')) if path.is_file()))
    print(json.dumps({'status':audit['status'],'files':len(artifacts),'bytes':sum(p.stat().st_size for p in out.rglob('*') if p.is_file())}))


if __name__=='__main__':main()
