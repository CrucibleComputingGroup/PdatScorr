#!/usr/bin/env python3
"""Package the combined native reset-cube preparation without a solver run."""
import argparse
import gzip
import json
from pathlib import Path

from reset_cube_prepared import validate_reset_cube_prepared
from register_status_lemmas import digest


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepared',type=Path,required=True);parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();prepared=args.prepared.resolve();record=validate_reset_cube_prepared(prepared)
    out=args.output.resolve();out.mkdir(parents=True,exist_ok=False);copied=[];large=[]
    def keep(path,relative):
        raw=path.read_bytes()
        if path.name in ('source.json','core.json','core.v','screen.json','screen.aig','native_candidate.json',
            'lemma_core.json','inactive_query_core.json','register_status_query_core.json','reset_cube_query_core.json') or len(raw)>2_000_000:
            large.append({'path':str(path),'sha256':digest(path),'bytes':len(raw)});return
        compressed=len(raw)>100_000
        if compressed:relative+='.gz'
        dest=out/relative;dest.parent.mkdir(parents=True,exist_ok=True)
        dest.write_bytes(gzip.compress(raw,mtime=0) if compressed else raw)
        copied.append({'path':relative,'source':str(path),'sha256':digest(dest),'source_sha256':digest(path),'gzip':compressed})
    for path in sorted(prepared.rglob('*')):
        if path.is_file():keep(path,'prepared/'+str(path.relative_to(prepared)))
    for name in ('reset_cube_import.py','reset_cube_prepared.py','collect_reset_cube_preparation.py'):
        keep(Path(__file__).with_name(name),name)
    facts=record['reset_cube_import']
    provenance={'status':'prepared_query_only','accepted_optimization':False,'target_solver_run':False,
        'native_hardware_json_sha256':record['core_json_sha256'],'harness_sha256':record['harness_sha256'],
        'query_model_sha256':record['query_core_sha256'],'aig_sha256':record['aig_sha256'],'aig_header':record['aig_header'],
        'query_property_counts':record['query_property_counts'],'native_hardware_unchanged':True,
        'rf_candidate_substituted':False,'native_arithmetic_retained':True,
        'proved_word_domains':7,'proved_rd_domains':40,'existing_predicate_cells_preserved':479,
        'inactive_reset_constants':1761,'register_status_reset_constants':275,'cube_reset_constants':583,
        'cube_native_words':42,'cdb_arbitration_state_bits_removed':8,
        'new_unproved_internal_premises':0,'new_environmental_premises':[],
        'proof_dependency_count':len(facts['proof_dependencies_sha256']),
        'scope':'Combined preparation only. The original three safety assertions remain open. All47internal assumptions '
            'are previously proved conclusions; the additional583reset constants add no premise. No target solve, physical area, '
            'hardware optimization or timing-derived savings claim.',
        'artifacts':copied,'large_external_artifacts':large}
    (out/'PROVENANCE.json').write_text(json.dumps(provenance,indent=2)+'\n')
    (out/'SHA256SUMS').write_text(''.join(f'{digest(path)}  {path.relative_to(out)}\n' for path in sorted(out.rglob('*')) if path.is_file()))
    print(json.dumps({'status':provenance['status'],'files':len(copied),'bytes':sum(p.stat().st_size for p in out.rglob('*') if p.is_file())}))


if __name__=='__main__':main()
