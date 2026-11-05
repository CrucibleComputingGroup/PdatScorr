#!/usr/bin/env python3
"""One bounded diagnostic on an already folded, source-bound GLA abstraction."""
import argparse
import json
from pathlib import Path
import re

from gate_pdr import rederive_map
from gate_solver import digest,header,quote,require,run_command
from solve_prepared import validate_prepared


def verdict(execution,log,status,frames):
    if execution['timeout'] or execution['returncode']!=0:return 'unknown_no_certificate'
    if re.search(r'\b(error|failed|segmentation fault|assertion failure)\b',log,re.I):return 'error'
    token=status.split()[0] if status.strip() else None
    cex=re.findall(r'Output\s+\d+\s+of miter .* was asserted in frame\s+(\d+)',log)
    bounded=re.findall(r'No output asserted in (\d+) frames\.',log)
    # This pinned ABC prints the generic conf-limit-0 footer on normal -F
    # completion. ConfLimit=0 disables that limit; do not mistake its Params
    # TimeOut field for an actual timeout. A real timeout footer still rejects.
    terminal='\n'.join(line for line in log.splitlines() if not line.startswith('Params:'))
    terminal=terminal.replace('Resource limit reached (conf limit 0).','')
    if token=='snl_SAT' and len(cex)==1 and not bounded:return 'counterexample_pending_validation'
    if (token in ('snl_UNK','snl_UNSAT') and len(bounded)==1 and int(bounded[0])>=frames and not cex and
        not re.search(r'timeout|time limit|resource limit|undecided',terminal,re.I)):
        return 'bounded_only_no_certificate'
    return 'unknown_no_certificate'


def run_bmc(aig,directory,*,frames=128,timeout=120,abc='/usr/local/bin/abc'):
    aig=Path(aig).resolve();out=Path(directory).resolve();out.mkdir(parents=True,exist_ok=False)
    values=header(aig);require(int(values[4])==1 and all(int(v)==0 for v in values[6:]),
        'Direct bounded search requires one ordinary output and no bad/constraint/fairness sections')
    binding=digest(aig);source=digest(Path(__file__))
    (out/'gate_bmc.py').write_bytes(Path(__file__).read_bytes())
    command=f'read_aiger {quote(aig)}; bmc3 -F {frames} -T {timeout} -v; write_status {quote(out/"bmc.status")}'
    execution=run_command([abc,'-c',command],out/'bmc.log',timeout+5)
    text=(out/'bmc.log').read_text();status=(out/'bmc.status').read_text() if (out/'bmc.status').exists() else ''
    result={'status':verdict(execution,text,status,frames),'accepted_optimization':False,'unbounded_certificate':False,
        'input_aig':str(aig),'input_sha256':binding,'input_header':values,'script_sha256':source,
        'execution':execution,'raw_status':status,'requested_frames':frames,'requested_seconds':timeout,
        'preprocessing':'None. Direct already-folded one-output abstraction; no assumptions, refolding, refinement, or native claim.'}
    if result['status']=='counterexample_pending_validation':
        validation=run_command([abc,'-c',f'read_aiger {quote(aig)}; &get; read_status {quote(out/"bmc.status")}; testcex; write_cex -a {quote(out/"counterexample.aiw")}'],out/'validate_cex.log',15)
        log=(out/'validate_cex.log').read_text();result['counterexample_validation']=validation
        result['status']='counterexample_in_abstraction_only' if (validation['returncode']==0 and not validation['timeout'] and
            re.search(r'And\s+AIG: The cex is correct\.',log) and not re.search(r'\b(error|failed)\b',log,re.I) and
            (out/'counterexample.aiw').exists()) else 'error'
        result['counterexample_frame']=int(re.search(r'was asserted in frame\s+(\d+)',text)[1])
    found=re.findall(r'No output asserted in (\d+) frames\.',text)
    result['reported_no_counterexample_frames']=int(found[0]) if len(found)==1 else None
    if digest(aig)!=binding or digest(Path(__file__))!=source:result.update(status='error',error='AIG or driver changed')
    result['artifact_sha256']={p.name:digest(p) for p in out.iterdir() if p.is_file()}
    (out/'summary.json').write_text(json.dumps(result,indent=2)+'\n');return result


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--gla-result',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True);p.add_argument('--abc',default='/usr/local/bin/abc')
    p.add_argument('--frames',type=int,default=128);p.add_argument('--timeout',type=int,default=120)
    a=p.parse_args();require(0<a.frames<=128 and 0<a.timeout<=120,'Diagnostic budget exceeds authorized bound')
    gla=a.gla_result.resolve();info=json.loads((gla/'summary.json').read_text())
    prepared=Path(info['prepared_directory']);model=validate_prepared(prepared)
    require(model['abstraction_mode']=='alu_mul' and model['query_property_counts']=={'assert':3,'assume':8,'cover':0},'Unexpected source query')
    dependencies={str(gla/'summary.json'):digest(gla/'summary.json'),str(prepared/'summary.json'):digest(prepared/'summary.json')}
    require(dependencies[str(prepared/'summary.json')]==info['prepared_summary_sha256'],'Prepared record changed')
    for name,expected in info['artifacts_sha256'].items():
        require(digest(gla/name)==expected,'GLA artifact changed: '+name);dependencies[str(gla/name)]=expected
    require(info['input_aig_sha256']==model['aig_sha256']==digest(Path(info['input_aig'])),'GLA source differs')
    require(info['derive']['returncode']==0 and not info['derive']['timeout'],'GLA map derivation failed')
    require(header(gla/'abstracted.aig')==info['abstracted_header'],'Abstraction header changed')
    out=a.output.resolve();out.mkdir(parents=True,exist_ok=False)
    replay=rederive_map(gla/'final_map.aig',gla/'abstracted.aig',out/'map_replay',abc=a.abc)
    validate_prepared(prepared)
    for path,expected in dependencies.items():require(digest(Path(path))==expected,'Dependency changed before BMC')
    result=run_bmc(gla/'abstracted.aig',out/'bmc',frames=a.frames,timeout=a.timeout,abc=a.abc)
    result.update(gate_map_replay=replay,source_dependencies_sha256=dependencies,
        source_prepared_directory=str(prepared),gla_result_directory=str(gla))
    try:
        validate_prepared(prepared)
        for path,expected in dependencies.items():require(digest(Path(path))==expected,'Source dependency changed during BMC')
    except (ValueError,OSError) as error:result.update(status='error',error=str(error))
    (out/'summary.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'frames':result['reported_no_counterexample_frames'],
        'counterexample_frame':result.get('counterexample_frame'),'accepted_optimization':False}))


if __name__=='__main__':main()
