#!/usr/bin/env python3
"""Package existing explicit-PDR map checks; never invoke a solver."""
import argparse
import gzip
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE.parents[3]),str(HERE)]
from odc.temporal import digest
from solve_prepared import validate_prepared


def read(path):return json.loads(path.read_text())


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--run',type=Path,required=True);ap.add_argument('--toys',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    run=args.run.resolve();toys=args.toys.resolve();result=read(run/'summary.json');tests=read(toys/'summary.json')
    assert result['accepted_optimization'] is False and tests['status']=='three_derived_map_tests_passed'
    assert result['script_sha256']==tests['driver_sha256']==digest(run/'pdr/gate_pdr.py')
    for path,expected in result['source_dependencies_sha256'].items():assert digest(Path(path))==expected,path
    for name,expected in result['artifacts_sha256'].items():assert digest(run/'pdr'/name)==expected,name
    for case in tests['cases']:
        path=toys/case['case']/'pdr';item=read(path/'summary.json')
        assert item['status']==case['status'] and digest(path/'summary.json')==case['summary_sha256']
        for name,expected in item['artifacts_sha256'].items():assert digest(path/name)==expected
    replay=result['gate_map_replay'];assert replay['abstracted_sha256']==replay['rederived_sha256']
    assert digest(run/'map_replay/rederived.aig')==replay['rederived_sha256']
    assert digest(Path(result['input_aig']))==result['input_sha256']==replay['abstracted_sha256']
    prepared=Path(result['source_prepared_directory']);native=validate_prepared(prepared)
    out=args.output.resolve();out.mkdir(parents=True,exist_ok=False);artifacts=[]
    def keep(path,relative):
        raw=path.read_bytes();compress=path.suffix=='.aig' or len(raw)>100_000
        if compress:relative+='.gz'
        target=out/relative;target.parent.mkdir(parents=True,exist_ok=True)
        target.write_bytes(gzip.compress(raw,mtime=0) if compress else raw)
        artifacts.append({'path':relative,'sha256':digest(target),'source':str(path),'source_sha256':digest(path),'gzip':compress})
    for directory,prefix in ((run,'query'),(toys,'toys')):
        for path in sorted(directory.rglob('*')):
            if path.is_file():keep(path,prefix+'/'+str(path.relative_to(directory)))
    gla=Path(result['gla_result_directory'])
    keep(gla/'summary.json','source_gla_summary.json');keep(prepared/'summary.json','source_prepared_summary.json')
    keep(Path(__file__),'collector_source.py')
    record={'status':result['status'],'accepted_optimization':False,
        'exact_gate_map_replay':True,'query_preprocessing':result['preprocessing'],
        'input_header':result['input_header'],'input_sha256':result['input_sha256'],
        'native_hardware_json_sha256':native['core_json_sha256'],'toy_outcomes':tests['cases'],
        'source_gate_map':{'sha256':replay['map_sha256'],
            'packaged_path':'../gate_solver_v1/query/final_map.aig.gz','original_path':replay['map_path']},
        'interpretation':'The recorded PDR query is over a source-bound gate-level overapproximation. An unknown result proves no admission bound; a counterexample is abstraction-only unless concretized. The positive/negative/spurious toy checks enforce this distinction. Native hardware remains unchanged.',
        'artifacts':artifacts}
    (out/'PROVENANCE.json').write_text(json.dumps(record,indent=2)+'\n')
    (out/'SHA256SUMS').write_text(''.join(f'{digest(p)}  {p.relative_to(out)}\n' for p in sorted(out.rglob('*')) if p.is_file()))
    print(json.dumps({'status':result['status'],'files':len(artifacts),'bytes':sum(p.stat().st_size for p in out.rglob('*') if p.is_file())}))


if __name__=='__main__':main()
