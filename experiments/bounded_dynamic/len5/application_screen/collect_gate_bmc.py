#!/usr/bin/env python3
"""Collect the single bounded map diagnostic and its two tiny engine controls."""
import argparse
import gzip
import json
from pathlib import Path

from gate_bmc import digest,require
from solve_prepared import validate_prepared


def read(path):return json.loads(path.read_text())


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--run',type=Path,required=True)
    p.add_argument('--toys',type=Path,required=True);p.add_argument('--tests',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    run=a.run.resolve();toys=a.toys.resolve();record=read(run/'summary.json')
    require(not record['accepted_optimization'] and not record['unbounded_certificate'],'Unexpected certificate')
    prepared=Path(record['source_prepared_directory']);native=validate_prepared(prepared)
    for path,expected in record['source_dependencies_sha256'].items():require(digest(Path(path))==expected,'Source dependency changed')
    for name,expected in record['artifact_sha256'].items():require(digest(run/'bmc'/name)==expected,'BMC artifact changed')
    replay=record['gate_map_replay']
    require(digest(run/'map_replay/rederived.aig')==record['input_sha256']==replay['abstracted_sha256']==replay['rederived_sha256'],'Map replay mismatch')
    cases=[]
    for index,expected in [(0,'bounded_only_no_certificate'),(1,'counterexample_in_abstraction_only')]:
        path=toys/f'test_real_bounded_positive_and{index}';test=read(path/'bmc/summary.json')
        require(test['status']==expected and test['script_sha256']==record['script_sha256'],'Smoke outcome/driver differs')
        for name,sha in test['artifact_sha256'].items():require(digest(path/'bmc'/name)==sha,'Smoke artifact changed')
        cases.append({'directory':path,'status':expected,'summary_sha256':digest(path/'bmc/summary.json')})
    out=a.output.resolve();out.mkdir(parents=True,exist_ok=False);files=[]
    def keep(path,relative):
        raw=path.read_bytes();compress=path.suffix=='.aig' or len(raw)>100000
        if compress:relative+='.gz'
        dest=out/relative;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(gzip.compress(raw,mtime=0) if compress else raw)
        require((gzip.decompress(dest.read_bytes()) if compress else dest.read_bytes())==raw,'Copy bytes differ')
        files.append({'path':relative,'sha256':digest(dest),'source':str(path),'source_sha256':digest(path),'gzip':compress})
    for path in sorted(run.rglob('*')):
        if path.is_file():keep(path,'query/'+str(path.relative_to(run)))
    for item in cases:
        for path in sorted(item['directory'].rglob('*')):
            if path.is_file():keep(path,'toys/'+item['directory'].name+'/'+str(path.relative_to(item['directory'])))
        item['directory']=str(item['directory'])
    keep(Path(record['gla_result_directory'])/'summary.json','source_gla_summary.json')
    keep(prepared/'summary.json','source_prepared_summary.json')
    keep(a.tests.resolve(),'test_gate_bmc.py');keep(Path(__file__).resolve(),'collector_source.py')
    manifest={'status':record['status'],'counterexample_frame':record.get('counterexample_frame'),
        'requested_frames':record['requested_frames'],'requested_seconds':record['requested_seconds'],
        'actual_solver_seconds':record['execution']['seconds'],'accepted_optimization':False,'unbounded_certificate':False,
        'source_prepared_and_transitive_dependencies_revalidated':True,'exact_map_replay':True,
        'input_header':record['input_header'],'input_sha256':record['input_sha256'],
        'native_hardware_sha256':native['core_json_sha256'],'toy_outcomes':cases,
        'source_gate_map':{'sha256':replay['map_sha256'],'original_path':replay['map_path'],
            'existing_compact_copy':'../gate_solver_v1/query/final_map.aig.gz'},
        'interpretation':'Validated counterexample belongs only to the recorded GLA abstraction. It explains why this abstract model cannot have a safety proof, but is neither a native-core counterexample nor a refinement result. No additional search was launched. Bounded absence would never be a certificate.',
        'artifacts':files}
    (out/'PROVENANCE.json').write_text(json.dumps(manifest,indent=2)+'\n')
    (out/'SHA256SUMS').write_text(''.join(f'{digest(f)}  {f.relative_to(out)}\n' for f in sorted(out.rglob('*')) if f.is_file()))
    print(json.dumps({'status':manifest['status'],'files':sum(f.is_file() for f in out.rglob('*')),
        'bytes':sum(f.stat().st_size for f in out.rglob('*') if f.is_file())}))


if __name__=='__main__':main()
