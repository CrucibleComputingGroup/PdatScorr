#!/usr/bin/env python3
"""Archive normal-GLA continuation and its checked tiny controls, without tools."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path

from gate_resume import aig_parts,digest,require
from solve_prepared import validate_prepared


def read(path):return json.loads(path.read_text())


def check(directory):
    result=read(directory/'summary.json');require(not result['accepted_optimization'],'Unexpected hardware acceptance')
    for p,sha in result['source_sha256'].items():require(digest(Path(p))==sha,'Changed continuation input')
    for name,sha in result['artifact_sha256'].items():require(digest(directory/name)==sha,'Changed continuation artifact')
    audit=result['input_audit'];graph,gate=aig_parts(directory/'loaded_map.aig')
    require(hashlib.sha256(graph).hexdigest()==audit['original_ordered_graph_sha256'] and
            hashlib.sha256(gate['g']).hexdigest()==audit['gate_classes_sha256'],'Loaded graph/classes no longer match audited source')
    require(audit['exact_original_graph_preserved'] and audit['exact_gate_classes_preserved'] and audit['read_warnings_absent'],'Input audit missing')
    require(result['reunrolled_from_frame_zero'] and result['no_new_premises_or_refolding'],'Continuation altered domain')
    return result


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--run',type=Path,required=True)
    p.add_argument('--toys',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();run=a.run.resolve();result=check(run);prepared=Path(result['source_prepared_directory'])
    validate_prepared(prepared)
    for path,sha in result['source_dependencies_sha256'].items():require(digest(Path(path))==sha,'Changed transitive dependency')
    source_replay=read(run/'source_replay/summary.json')
    require(source_replay['full_file_byte_identical'] and source_replay['replay_is_solver_free'],'Original folded export replay missing')
    require((run/'source_replay/replayed_folded.aig').read_bytes()==(Path(result['source_gla_directory'])/'folded.aig').read_bytes(),
            'Prepared-source folded export differs from saved original graph')
    cases=[]
    for name,expected in [('spurious','proved_safety_query_only'),('negative','counterexample_in_original_saved_query_model')]:
        directory=a.toys.resolve()/name;toy=check(directory)
        require(toy['status']==expected,'Tiny control did not yield expected strict outcome')
        require(toy['source_sha256'][str(Path(__file__).resolve().with_name('gate_resume.py'))]==result['source_sha256'][str(Path(__file__).resolve().with_name('gate_resume.py'))], 'Control/target driver differ')
        cases.append({'name':name,'status':expected,'summary_sha256':digest(directory/'summary.json')})
    out=a.output.resolve();out.mkdir(parents=True,exist_ok=False);files=[]
    def keep(path,name):
        raw=path.read_bytes();compress=path.suffix=='.aig' or len(raw)>100000
        if compress:name+='.gz'
        dest=out/name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(gzip.compress(raw,mtime=0) if compress else raw)
        files.append({'path':name,'sha256':digest(dest),'source':str(path),'source_sha256':digest(path),'gzip':compress})
    for directory,prefix in [(run,'query'),(a.toys.resolve(),'toys')]:
        for path in sorted(directory.rglob('*')):
            if path.is_file():keep(path,prefix+'/'+str(path.relative_to(directory)))
    keep(prepared/'summary.json','source_prepared_summary.json')
    keep(Path(result['source_gla_directory'])/'summary.json','source_gla_summary.json')
    keep(Path(__file__).resolve(),'collector_source.py')
    here=Path(__file__).resolve().parent
    require(digest(here/'gate_solver.py')==digest(Path(result['source_gla_directory'])/'gate_solver.py'),
            'Live GLA verdict helper differs from source-bound archived version')
    helpers={}
    for name in ('gate_solver.py','solve_prepared.py'):
        keep(here/name,'helpers/'+name);helpers[name]=digest(here/name)
    tests=Path(__file__).resolve().parents[4]/'tests/unit/test_gate_resume.py';keep(tests,'test_gate_resume.py')
    manifest={'status':result['status'],'accepted_optimization':False,'requested_seconds':result['requested_seconds'],
        'solver_seconds':result['execution']['seconds'],'raw_status':result['raw_status'],
        'input_audit':result['input_audit'],'toy_outcomes':cases,
        'original_graph_and_gate_classes_loaded_exactly':True,'reunrolled_from_frame_zero':True,
        'prepared_to_folded_export_replay':source_replay,
        'no_additional_environment_or_internal_assumptions':True,'transitive_source_dependencies_rechecked':True,
        'live_helper_sha256_at_collection':helpers,'live_gla_helper_equals_original_archived_helper':True,
        'interpretation':'Normal GLA continuation of the original folded proof-model graph, using prior gate classes. Explicit unbounded proof or original-folded-model-validated CEX required for a decisive verdict. Unknown, stable-map and bounded progress prove nothing. Original model contains ALU/multiplier cuts, so CEX is not automatically native RTL.',
        'artifacts':files}
    (out/'PROVENANCE.json').write_text(json.dumps(manifest,indent=2)+'\n')
    (out/'SHA256SUMS').write_text(''.join(f'{digest(f)}  {f.relative_to(out)}\n' for f in sorted(out.rglob('*')) if f.is_file()))
    print(json.dumps({'status':result['status'],'files':sum(f.is_file() for f in out.rglob('*')),
        'bytes':sum(f.stat().st_size for f in out.rglob('*') if f.is_file())}))


if __name__=='__main__':main()
