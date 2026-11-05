#!/usr/bin/env python3
"""Resume normal GLA from an exact saved gate map, re-unrolling from frame 0."""
import argparse
import hashlib
import json
from pathlib import Path
import re

from gate_solver import digest,header,quote,require,run_command,verdict
from solve_prepared import validate_prepared


def aig_parts(path):
    """Exact ordered binary-AIG graph plus ABC extension bytes; never rewrite."""
    data=Path(path).read_bytes();cursor=data.index(b'\n')+1;words=data[:cursor].split()
    require(words[0]==b'aig' and len(words)==6,'Expected ordinary binary AIG without constraint/property sections')
    maximum,inputs,latches,outputs,ands=map(int,words[1:]);require(outputs==1,'Expected one folded bad output')
    require(maximum==inputs+latches+ands,'Unexpected noncontiguous AIG variables')
    for _ in range(latches+outputs):cursor=data.index(b'\n',cursor)+1
    for _ in range(2*ands):
        while data[cursor]&128:cursor+=1
        cursor+=1
    graph=data[:cursor];require(data[cursor:cursor+1]==b'c','Unexpected symbol table or missing ABC extension marker');cursor+=1
    extensions={}
    while cursor<len(data) and data[cursor:cursor+1]!=b'\n':
        tag=data[cursor:cursor+1].decode('ascii');cursor+=1
        require(tag not in extensions and cursor+4<=len(data),'Malformed/duplicate ABC extension')
        size=int.from_bytes(data[cursor:cursor+4],'big');cursor+=4
        require(cursor+size<=len(data),'Truncated ABC extension');extensions[tag]=data[cursor:cursor+size];cursor+=size
    require('c' not in extensions,'Unfolded constraints in extension metadata')
    if 'g' in extensions:require(len(extensions['g'])==4*(maximum+outputs+latches+1),'Gate-class indexing differs from original GIA object count')
    return graph,extensions


def audit_map(map_path,folded,abstracted,out,*,abc='/usr/local/bin/abc'):
    out.mkdir(parents=True,exist_ok=False);original,old=aig_parts(map_path);reference,_=aig_parts(folded)
    require(original==reference,'Saved map no longer contains exact original ordered GIA graph')
    require('g' in old and any(old['g']),'Missing previous gate classes')
    command=f'&read -s {quote(map_path)}; &write -s {quote(out/"roundtrip_map.aig")}; &gla_derive; &write -s {quote(out/"derived.aig")}'
    execution=run_command([abc,'-c',command],out/'audit.log',20)
    log=(out/'audit.log').read_text();require(execution['returncode']==0 and not execution['timeout'],'Map input audit failed')
    require(not re.search(r'warning|error|invalid|missing|skipping|no AIG|already solved',log,re.I),'Unsafe map read/derivation warning')
    graph,new=aig_parts(out/'roundtrip_map.aig');require(graph==original and new.get('g')==old['g'],'Read altered original graph or previous gate classes')
    require({k:v for k,v in new.items() if k!='n'}=={k:v for k,v in old.items() if k!='n'},'Read altered non-name metadata')
    require(aig_parts(out/'derived.aig')[0]==aig_parts(abstracted)[0],'Read changed exact derived abstraction graph/PI ordering')
    return {'execution':execution,'source_map_sha256':digest(map_path),'source_folded_sha256':digest(folded),
        'source_abstracted_sha256':digest(abstracted),'original_ordered_graph_sha256':hashlib.sha256(original).hexdigest(),
        'gate_classes_sha256':hashlib.sha256(old['g']).hexdigest(),'gate_class_bytes':len(old['g']),
        'exact_original_graph_preserved':True,'exact_gate_classes_preserved':True,'read_warnings_absent':True,
        'derived_graph_sha256':hashlib.sha256(aig_parts(abstracted)[0]).hexdigest()}


def resume(map_path,folded,abstracted,out,*,abc='/usr/local/bin/abc',timeout=600):
    out.mkdir(parents=True,exist_ok=False)
    inputs={str(Path(p).resolve()):digest(p) for p in (map_path,folded,abstracted,Path(__file__))}
    audited=audit_map(map_path,folded,abstracted,out/'input_audit',abc=abc)
    command=(f'&read -s {quote(map_path)}; &write -s {quote(out/"loaded_map.aig")}; '
             f'&gla -q -T {timeout} -v -m -A {quote(out/"progress_map.aig")} -L {quote(out/"gla.status")}; '
             f'write_status {quote(out/"final.status")}; &write -s {quote(out/"final_map.aig")}')
    execution=run_command([abc,'-c',command],out/'gla.log',timeout+10)
    log=(out/'gla.log').read_text();raw=(out/'final.status').read_text() if (out/'final.status').exists() else ''
    status=verdict(execution,log,raw)
    if re.search(r'warning|invalid|missing|skipping previously',log,re.I):status='error'
    require('Skip = 0' in log,'GLA did not explicitly re-unroll without frame skipping')
    old_graph,old_ext=aig_parts(map_path);loaded_graph,loaded_ext=aig_parts(out/'loaded_map.aig')
    require(loaded_graph==old_graph and loaded_ext.get('g')==old_ext['g'],'Solver did not load preserved map')
    record={'status':status,'accepted_optimization':False,'requested_seconds':timeout,'execution':execution,'raw_status':raw,
        'input_audit':audited,'source_sha256':inputs,'input_header':header(map_path),'reunrolled_from_frame_zero':True,
        'no_new_premises_or_refolding':True,'original_folded_model':str(folded),
        'scope':'Normal CEGAR on original saved proof-model graph with existing gate classes. Query has prior ALU/multiplier abstractions; no native RTL claim.'}
    if status=='counterexample_pending_validation':
        validation=run_command([abc,'-c',f'read_aiger {quote(folded)}; &get; read_status {quote(out/"final.status")}; testcex; write_cex -a {quote(out/"counterexample.aiw")}'],out/'validate_cex.log',15)
        text=(out/'validate_cex.log').read_text();record['counterexample_validation']=validation
        record['status']='counterexample_in_original_saved_query_model' if (validation['returncode']==0 and not validation['timeout'] and
            re.search(r'And\s+AIG: The cex is correct\.',text) and not re.search(r'error|failed|invalid',text,re.I) and (out/'counterexample.aiw').exists()) else 'error'
    for name in ('final_map.aig','progress_map.aig'):
        if (out/name).exists():
            graph,_=aig_parts(out/name);require(graph==old_graph,'Refinement changed underlying original GIA graph')
    require(all(digest(Path(p))==sha for p,sha in inputs.items()),'Source changed during continuation')
    (out/'gate_resume.py').write_bytes(Path(__file__).read_bytes())
    record['artifact_sha256']={p.name:digest(p) for p in out.iterdir() if p.is_file()}
    (out/'summary.json').write_text(json.dumps(record,indent=2)+'\n');return record


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--gla-result',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True);p.add_argument('--abc',default='/usr/local/bin/abc')
    p.add_argument('--timeout',type=int,default=600);a=p.parse_args();require(0<a.timeout<=600,'Budget outside authorized bound')
    gla=a.gla_result.resolve();info=json.loads((gla/'summary.json').read_text());prepared=Path(info['prepared_directory'])
    model=validate_prepared(prepared);require(model['abstraction_mode']=='alu_mul' and model['query_property_counts']=={'assert':3,'assume':8,'cover':0},'Unexpected original query')
    dependencies={str(gla/'summary.json'):digest(gla/'summary.json'),str(prepared/'summary.json'):digest(prepared/'summary.json')}
    require(dependencies[str(prepared/'summary.json')]==info['prepared_summary_sha256'],'Prepared source record changed')
    for name,expected in info['artifacts_sha256'].items():
        require(digest(gla/name)==expected,'GLA artifact changed');dependencies[str(gla/name)]=expected
    require(info['input_aig_sha256']==model['aig_sha256']==digest(Path(info['input_aig'])),'Original GLA source differs')
    result=resume(gla/'final_map.aig',gla/'folded.aig',gla/'abstracted.aig',a.output.resolve(),abc=a.abc,timeout=a.timeout)
    result.update(source_dependencies_sha256=dependencies,source_prepared_directory=str(prepared),source_gla_directory=str(gla))
    try:
        validate_prepared(prepared)
        for path,expected in dependencies.items():require(digest(Path(path))==expected,'Source dependency changed')
    except (ValueError,OSError) as error:result.update(status='error',error=str(error))
    (a.output/'summary.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'accepted_optimization':False}))


if __name__=='__main__':main()
