#!/usr/bin/env python3
"""Collect an inspected theorem-assisted query and its solver attempts; no runs."""
import argparse
import gzip
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE.parents[3]), str(HERE)]
from odc.temporal import digest
from solve_prepared import validate_prepared


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--prepared', type=Path, required=True)
    ap.add_argument('--solver', type=Path, action='append', required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args(); prepared = args.prepared.resolve()
    summary = validate_prepared(prepared)
    if not summary['native_word_domain_import'] or not summary['external_rom_domain_import']:
        raise ValueError('This collector requires the complete theorem composition')
    solvers=[]
    for directory in args.solver:
        directory=directory.resolve(); record=json.loads((directory/'summary.json').read_text())
        assert record['prepared_directory'] == str(prepared)
        assert record['prepared_summary_sha256'] == digest(prepared/'summary.json')
        assert record['aig_sha256'] == summary['aig_sha256'] and record['accepted_optimization'] is False
        assert digest(directory/'solve_prepared.py') == record['script_sha256']
        assert digest(directory/(record['engine']+'.log')) == record['execution']['log_sha256']
        assert record['query_property_counts'] == {'assert':3,'assume':8,'cover':0}
        solvers.append((directory,record))
    out=args.output.resolve();out.mkdir(parents=True,exist_ok=False)
    copied=[];large=[]
    def keep(path,relative):
        raw=path.read_bytes()
        if path.name in ('source.json','core.json','core.v','lemma_core.json','abstract_query_core.json','screen.json','screen.aig','native_candidate.json') or len(raw)>2_000_000 and path.suffix!='.log':
            large.append({'path':str(path),'sha256':digest(path),'bytes':len(raw)})
            return
        compress=path.suffix=='.log' and len(raw)>100_000
        if compress:relative+='.gz'
        dst=out/relative;dst.parent.mkdir(parents=True,exist_ok=True)
        dst.write_bytes(gzip.compress(raw,mtime=0) if compress else raw)
        copied.append({'path':relative,'sha256':digest(dst),'source':str(path),'source_sha256':digest(path),'gzip':compress})
    for path in sorted(prepared.rglob('*')):
        if path.is_file():keep(path,'prepared/'+str(path.relative_to(prepared)))
    for directory,_ in solvers:
        for path in sorted(directory.rglob('*')):
            if path.is_file():keep(path,'solvers/'+directory.name+'/'+str(path.relative_to(directory)))
    keep(Path(__file__),'collector_source.py')
    record={'status':'theorem_assisted_query_evidence','accepted_optimization':False,
        'solver_outcomes':[{'engine':r['engine'],'status':r['status'],'seconds':r['execution']['seconds'],
                            'requested_frames':r['requested_frames']} for _,r in solvers],
        'native_source_sha256':summary['source_json_sha256'],'native_core_sha256':summary['core_json_sha256'],
        'query_only_model_sha256':summary['query_core_sha256'],'query_property_counts':summary['query_property_counts'],
        'native_hardware_contains_formal_properties':False,'data_abstraction':summary['abstraction_mode'],
        'native_word_theorem_count':7,'new_unproved_internal_premises':0,
        'external_rom_theorem_sha256':summary['external_rom_domain_import']['certificate_sha256'],
        'interpretation':'Seven source-bound unbounded instruction-domain theorems are proof-only consequences of the exact ROM/reset environment. Three original safety properties remain obligations. No hardware rewrite, storage saving, or area credit follows from an unknown or bounded result.',
        'large_artifacts':large,'artifacts':copied}
    (out/'PROVENANCE.json').write_text(json.dumps(record,indent=2)+'\n')
    (out/'SHA256SUMS').write_text(''.join(f'{digest(p)}  {p.relative_to(out)}\n' for p in sorted(out.rglob('*')) if p.is_file()))
    print(json.dumps({'files':len(copied),'solver_outcomes':record['solver_outcomes']}))


if __name__=='__main__':main()
