#!/usr/bin/env python3
"""Package the completed48-premise native GLA diagnostic and qualification."""
import argparse
import gzip
import json
from pathlib import Path
import re

from combined_gate_solver import validate_combined
from collect_gate_solver import check_result
from gate_solver import digest,require


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--query',type=Path,required=True);parser.add_argument('--source-audit',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();query=args.query.resolve();audit=args.source_audit.resolve()
    require(__debug__,'Collector must run with Python assertions enabled')
    result=json.loads((query/'summary.json').read_text());engine=check_result(query/'gla')
    require(result['status']==engine['status'] and result['post_run_dependencies_verified'] is True,
            'Wrapper/engine result mismatch or postcheck failure')
    require(digest(query/'gla/summary.json')==result['gla_summary_sha256'],'Engine record changed')
    prepared=Path(result['prepared_directory']);model,deps=validate_combined(prepared)
    require(deps==result['proof_dependencies_sha256'] and digest(prepared/'summary.json')==result['prepared_summary_sha256'],
            'Preparation/dependency closure changed')
    require(model['aig_sha256']==engine['input_aig_sha256'],'Solved input differs')
    for key in ('wrapper_dependencies_sha256','tool_dependencies_sha256'):
        for path,expected in result[key].items():require(digest(Path(path))==expected,'Driver/tool changed: '+path)
    for path,expected in result['wrapper_artifacts_sha256'].items():
        require(digest(query/path)==expected,'Wrapper snapshot changed: '+path)
    qualification=query/'qualification';qual=json.loads((qualification/'summary.json').read_text())
    require(digest(qualification/'summary.json')==result['qualification_summary_sha256'] and qual['status']=='qualified',
            'Qualification record changed')
    for path,expected in qual['artifacts_sha256'].items():require(digest(qualification/path)==expected,'Qualification changed')
    for name,count,status in [('all48',48,'proved_safety_query_only'),('without_last',47,'counterexample_in_query_model')]:
        toy=check_result(qualification/(name+'_gla'))
        require(toy['status']==status and int(toy['input_header'][7])==count,'Qualification verdict/inventory changed')
        require(toy['script_sha256']==engine['script_sha256'],'Toy/target engine changed')
        require(toy['execution']['executable_sha256']==engine['execution']['executable_sha256'],'Toy/target ABC changed')
    source=json.loads((audit/'summary.json').read_text())
    require(source['installed_abc_sha256']==engine['execution']['executable_sha256'],'Audited ABC differs')
    output=args.output.resolve();output.mkdir(parents=True,exist_ok=False);artifacts=[]
    def keep(path,relative):
        raw=path.read_bytes();compressed=path.suffix=='.aig' or len(raw)>100_000
        if compressed:relative+='.gz'
        target=output/relative;target.parent.mkdir(parents=True,exist_ok=True)
        target.write_bytes(gzip.compress(raw,mtime=0) if compressed else raw)
        artifacts.append(dict(path=relative,source=str(path),source_sha256=digest(path),sha256=digest(target),gzip=compressed))
    for directory,prefix in [(query,'query'),(audit,'source_audit')]:
        for path in sorted(directory.rglob('*')):
            if path.is_file():keep(path,prefix+'/'+str(path.relative_to(directory)))
    keep(prepared/'summary.json','prepared_summary.json');keep(Path(__file__),'collector_source.py')
    log=(query/'gla/gla.log').read_text()
    timeout=re.search(r'GLA reached timeout (\d+) sec in frame (\d+) with a (\d+)-stable abstraction',log)
    calls=re.search(r'Concurrent calls = (\d+)',log)
    provenance=dict(status=result['status'],accepted_optimization=False,
        requested_seconds=result['requested_seconds'],execution_seconds=engine['execution']['seconds'],
        native_hardware_json_sha256=model['core_json_sha256'],query_model_sha256=model['query_core_sha256'],
        input_aig_sha256=engine['input_aig_sha256'],input_header=engine['input_header'],
        folded_header=engine.get('folded_header'),abstracted_header=engine.get('abstracted_header'),
        query_property_counts=model['query_property_counts'],proof_dependency_count=len(deps),
        native_arithmetic_retained=True,new_environmental_premises=[],new_unproved_internal_premises=0,
        tiny_qualification='All48constraints proved; omitting only48th yielded testcex-validated query counterexample.',
        timeout_frame=int(timeout[2]) if timeout else None,stable_frames_at_timeout=int(timeout[3]) if timeout else None,
        proof_thread_calls=int(calls[1]) if calls else None,source_identity_caveat=source['source_identity_caveat'],
        scope=result['native_query_scope'],interpretation='Only an explicit unbounded verdict establishes this safety query. '
            'Maps, stability, bounded success and timeout are not certificates or hardware savings. No automatic follow-on solve.',
        artifacts=artifacts)
    (output/'PROVENANCE.json').write_text(json.dumps(provenance,indent=2)+'\n')
    (output/'SHA256SUMS').write_text(''.join(f'{digest(p)}  {p.relative_to(output)}\n' for p in sorted(output.rglob('*')) if p.is_file()))
    print(json.dumps(dict(status=result['status'],files=len(artifacts),bytes=sum(p.stat().st_size for p in output.rglob('*') if p.is_file()))))


if __name__=='__main__':main()
