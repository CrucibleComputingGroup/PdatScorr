#!/usr/bin/env python3
"""Read-only comparison of matched inactive-FU query preparations."""
import argparse
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE.parents[3]),str(HERE)]
from odc.temporal import digest
from solve_prepared import validate_prepared


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--abstract',type=Path,required=True);ap.add_argument('--native',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    a_dir,b_dir=args.abstract.resolve(),args.native.resolve()
    a,b=validate_prepared(a_dir),validate_prepared(b_dir)
    assert a['abstraction_mode']=='alu_mul' and b['abstraction_mode']=='none'
    same={}
    for name in ('source.json','core.json','core.v','AdmissionScreen.sv','lemma_core.json','inactive_query_core.json','formal_screen.py'):
        assert digest(a_dir/name)==digest(b_dir/name),name
        same[name]=digest(a_dir/name)
    assert Path(b['query_core_path']).resolve()==b_dir/'inactive_query_core.json'
    assert b['datapath_abstraction'] is None and b['abstraction_helper_sha256'] is None
    for record in (a,b):
        assert record['query_property_counts']=={'assert':3,'assume':8,'cover':0}
        assert record['inactive_fu_import']['status']=='inactive_fu_reset_facts_replayed'
        assert record['inactive_fu_import']['assumptions_added']==0
        assert len(record['inactive_fu_import']['reset_substitutions'])==1761
    assert a['inactive_fu_import']['reset_substitutions']==b['inactive_fu_import']['reset_substitutions']
    query=json.loads((b_dir/'inactive_query_core.json').read_text())['modules']['datapath']
    assert not any(name.startswith('$pscorr_proof_only_datapath_') for name in query['cells'])
    assert sum(c['type']=='$assume' for c in query['cells'].values())==7
    results=[]
    for directory,record in ((a_dir,a),(b_dir,b)):
        results.append({'directory':str(directory),'mode':record['abstraction_mode'],
            'summary_sha256':digest(directory/'summary.json'),'aig_sha256':record['aig_sha256'],
            'and_nodes':int(record['aig_header'][5]),'latches':int(record['aig_header'][3]),
            'inputs':int(record['aig_header'][2]),'dependency_count':len(record['inactive_fu_import']['proof_dependencies_sha256'])})
    result={'status':'matched_native_arithmetic_preparation_verified','accepted_optimization':False,
        'same_files_sha256':same,'properties':{'assert':3,'assume':8,'cover':0},'models':results,
        'native_payload_arithmetic_retained':True,'target_solver_executed':False,
        'and_delta_native_minus_abstract':results[1]['and_nodes']-results[0]['and_nodes'],
        'latch_delta_native_minus_abstract':results[1]['latches']-results[0]['latches'],
        'scope':'Preparation-only precision/cost comparison. Both models share exact native hardware, reset facts, ROM, timing, probes, and premises. Only the first applies payload overapproximation.'}
    out=args.output.resolve();out.mkdir(parents=True,exist_ok=False)
    (out/'compare_inactive_preparations.py').write_bytes(Path(__file__).read_bytes())
    (out/'summary.json').write_text(json.dumps(result,indent=2)+'\n')
    (out/'SHA256SUMS').write_text(''.join(f'{digest(p)}  {p.name}\n' for p in sorted(out.iterdir()) if p.is_file()))
    print(json.dumps({'status':result['status'],'models':results}))


if __name__=='__main__':main()
