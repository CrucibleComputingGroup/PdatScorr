#!/usr/bin/env python3
"""Explicit PDR on the exact proof-only abstraction exported by a GLA run."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import re
import sys

HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE.parents[3]),str(HERE)]
from odc.temporal import digest, run_command
from gate_solver import header, quote, require
from solve_prepared import validate_prepared


def run_pdr(aig, directory, *, abc='/usr/local/bin/abc', timeout=120):
    aig=Path(aig).resolve();directory=Path(directory).resolve();directory.mkdir(parents=True,exist_ok=False)
    values=header(aig)
    require(int(values[4])==1 and (len(values)<7 or int(values[6])==0) and (len(values)<8 or int(values[7])==0),
            'Direct abstraction PDR requires one ordinary bad output and no remaining constraints')
    binding=digest(aig);source=digest(Path(__file__))
    (directory/'gate_pdr.py').write_bytes(Path(__file__).read_bytes())
    command=(f'read_aiger {quote(aig)}; pdr -T {timeout} -v; write_status {quote(directory/"pdr.status")}')
    execution=run_command([abc,'-c',command],directory/'pdr.log',timeout+5)
    log=(directory/'pdr.log').read_text();status=(directory/'pdr.status').read_text() if (directory/'pdr.status').exists() else ''
    token=status.split()[0] if status.strip() else None
    result='unknown'
    if execution['returncode']==0 and not execution['timeout']:
        if (token=='snl_UNSAT' and len(re.findall(r'(?m)^Property proved\.',log))==1 and
            not re.search(r'\b(error|failed|undecided|disproved|timed out|time limit|was asserted)\b',log,re.I)):
            result='proved_overapproximation_safety'
        elif token=='snl_SAT' and re.search(r'Output\s+\d+\s+of miter .* was asserted in frame\s+\d+',log):
            result='counterexample_pending_validation'
    record={'status':result,'accepted_optimization':False,'input_aig':str(aig),'input_sha256':binding,
        'input_header':values,'script_sha256':source,'execution':execution,'raw_status':status,
        'preprocessing':'None: read the ordinary one-output abstraction directly; no fold, no extra assumptions',
        'interpretation':'A complete unbounded proof of the overapproximation transfers through the source-bound GLA map. A counterexample here belongs only to the abstraction until concretized against the original model.'}
    if result=='counterexample_pending_validation':
        check=(f'read_aiger {quote(aig)}; &get; read_status {quote(directory/"pdr.status")}; testcex; '
               f'write_cex -a {quote(directory/"counterexample.aiw")}')
        validation=run_command([abc,'-c',check],directory/'validate_cex.log',15)
        text=(directory/'validate_cex.log').read_text();record['counterexample_validation']=validation
        record['status']='counterexample_in_abstraction_only' if (validation['returncode']==0 and not validation['timeout'] and
            'And  AIG: The cex is correct.' in text and not re.search(r'\b(error|failed)\b',text,re.I) and
            (directory/'counterexample.aiw').exists()) else 'error'
        frame=re.search(r'was asserted in frame\s+(\d+)',log)
        record['counterexample_frame']=int(frame[1]) if frame else None
    if digest(aig)!=binding or digest(Path(__file__))!=source:record.update(status='error',error='AIG or driver changed during PDR')
    record['artifacts_sha256']={p.name:digest(p) for p in directory.iterdir() if p.is_file()}
    (directory/'summary.json').write_text(json.dumps(record,indent=2)+'\n')
    return record


def rederive_map(map_path, expected_aig, directory, *, abc='/usr/local/bin/abc'):
    """Replay only the exact gate-map derivation, without a solver."""
    map_path,expected_aig=Path(map_path).resolve(),Path(expected_aig).resolve()
    directory=Path(directory).resolve();directory.mkdir(parents=True,exist_ok=False)
    mapped=digest(map_path);expected=digest(expected_aig);out=directory/'rederived.aig'
    command=f'&read {quote(map_path)}; &gla_derive; &ps; &write -s {quote(out)}'
    execution=run_command([abc,'-c',command],directory/'derive.log',20)
    require(execution['returncode']==0 and not execution['timeout'], 'Gate map derivation did not finish')
    log=(directory/'derive.log').read_text()
    require(not re.search(r'error|missing|skipping|no AIG|already solved',log,re.I), 'Gate map was not actually applied')
    require(out.exists() and digest(out)==expected, 'Replayed gate abstraction differs from the recorded exact model')
    require(digest(map_path)==mapped and digest(expected_aig)==expected,'Gate map input changed during replay')
    return {'map_path':str(map_path),'map_sha256':mapped,'abstracted_path':str(expected_aig),
            'abstracted_sha256':expected,'rederived_sha256':digest(out),'execution':execution}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--gla-result',type=Path,required=True);ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--timeout',type=int,default=120);ap.add_argument('--abc',default='/usr/local/bin/abc')
    args=ap.parse_args();require(args.timeout>0,'Positive budget required')
    gla=args.gla_result.resolve();info=json.loads((gla/'summary.json').read_text())
    prepared=Path(info['prepared_directory']);model=validate_prepared(prepared)
    require(model['abstraction_mode']=='alu_mul' and model['query_property_counts']=={'assert':3,'assume':8,'cover':0},
            'Unexpected source safety query')
    dependencies={str(gla/'summary.json'):digest(gla/'summary.json'),str(prepared/'summary.json'):digest(prepared/'summary.json')}
    require(dependencies[str(prepared/'summary.json')]==info['prepared_summary_sha256'],'Original prepared query changed')
    for name,expected in info['artifacts_sha256'].items():
        require(digest(gla/name)==expected,'GLA artifact changed: '+name)
        dependencies[str(gla/name)]=expected
    require(info['input_aig_sha256']==model['aig_sha256']==digest(Path(info['input_aig'])),'GLA input differs from prepared source')
    require(info['derive']['returncode']==0 and not info['derive']['timeout'],'Recorded abstraction derivation failed')
    require(header(gla/'abstracted.aig')==info['abstracted_header'],'Derived header changed')
    out=args.output.resolve();out.mkdir(parents=True,exist_ok=False)
    replay=rederive_map(gla/'final_map.aig',gla/'abstracted.aig',out/'map_replay',abc=args.abc)
    result=run_pdr(gla/'abstracted.aig',out/'pdr',abc=args.abc,timeout=args.timeout)
    result['gate_map_replay']=replay;result['source_dependencies_sha256']=dependencies
    result['source_prepared_directory']=str(prepared);result['gla_result_directory']=str(gla)
    try:
        validate_prepared(prepared)
        for path,expected in dependencies.items():require(digest(Path(path))==expected,'Source GLA dependency changed: '+path)
    except (ValueError,OSError) as error:result.update(status='error',error=str(error))
    (out/'summary.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'accepted_optimization':False}))


if __name__=='__main__':main()
