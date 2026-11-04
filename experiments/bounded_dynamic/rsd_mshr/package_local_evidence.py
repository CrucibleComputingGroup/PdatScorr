#!/usr/bin/env python3
"""Copy compact local proof/cover/audit and validated functional-negative records."""
import argparse
import json
from pathlib import Path
import shutil
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[2]))
from odc.temporal import digest


def package(output, items, scope):
    if output.exists():
        raise SystemExit('Refusing existing package: '+str(output))
    output.mkdir(parents=True)
    manifest = {'status':'complete', 'scope':scope, 'files':{}}
    for source, relative in items:
        target = output/relative
        target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copy2(source,target)
        assert source.read_bytes() == target.read_bytes()
        manifest['files'][str(relative)] = {'source':str(source.relative_to(HERE)),
            'sha256':digest(target),'bytes':target.stat().st_size}
    manifest['total_bytes'] = sum(v['bytes'] for v in manifest['files'].values())
    (output/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--local-output',type=Path,default=HERE/'evidence/local')
    parser.add_argument('--negative-output',type=Path,default=HERE/'evidence/negative')
    args = parser.parse_args()
    if args.local_output.exists() or args.negative_output.exists():
        raise SystemExit('Both package outputs must be fresh')
    results = HERE/'results'
    positive = json.loads((results/'odc_pdr_v4/report.json').read_text())
    local = json.loads((results/'local_evidence_v2.json').read_text())
    boundary = json.loads((results/'boundary_audit_v1/summary.json').read_text())
    assert positive['status']=='proved' and positive['combined_proof']['proven']
    assert local['status']==boundary['status']=='passed'
    assert local['baseline_json_sha256']==boundary['baseline_json_sha256']==positive['design_sha256']
    local_items = [(results/'local_evidence_v2.json',Path('summary.json')),
                   (results/'source_proof_review_v1.txt',Path('source_proof_review.txt'))]
    names = ['summary.json','MshrTimingProof.sv','ReadServiceContract.sv',
             'invariant_bindings.json','base.log','induction.log','cover.log',
             'elaborate.log','proof.ys','proof_export.ys','proof_export.log',
             *[f'cover_{i}.vcd' for i in range(4)]]
    for name in names:
        local_items.append((results/'proof_v6'/name,Path('proof')/name))
    for source in sorted((results/'boundary_audit_v1').rglob('*')):
        if source.is_file():
            local_items.append((source,Path('boundary_audit')/source.relative_to(results/'boundary_audit_v1')))
    local_manifest = package(args.local_output,local_items,
        'Final native component local mechanism proof and nonvacuity covers; source audit. Historical extra-throttle negative rows in summary are labeled and are not the final negative evidence.')

    negative_items = []
    for label,dirname in [('deadline','auto_negative_deadline_v1'),('order','auto_negative_order_v1')]:
        run = results/dirname
        summary = json.loads((run/'summary.json').read_text())
        witness = json.loads((run/'witness/summary.json').read_text())
        assert summary['status']=='functional_counterexample'
        assert witness['status']=='validated_functional_counterexample'
        assert summary['baseline_json_sha256']==positive['design_sha256']
        assert summary['reference_sha256']==positive['combined_proof']['reference_sha256']
        assert summary['candidate_sha256']==positive['combined_proof']['candidate_sha256']
        assert witness['negative_summary_sha256']==digest(run/'summary.json')
        assert summary['functional_assertions']==14 and not summary['assert_state_correspondence']
        for name,h in witness['artifact_sha256'].items():
            assert digest(run/'witness'/name)==h
        names=['summary.json','harness.sv','temporal_source.py',
               *['proof/'+x for x in ['proof.json','prepare.ys','prepare.log','aig_export.ys','aig_export.log','pdr.log']],
               *['witness/'+x for x in ['summary.json','abc.log','run.abc','counterexample.aiw','counterexample.txt']]]
        # Full miter JSON/SMT/AIG graphs and the replay-only folded AIG remain
        # outside the compact package. Witness hashes and reconstruction
        # commands bind the retained machine-readable counterexamples.
        for name in names:
            negative_items.append((run/name,Path(label)/name))
    negative_manifest = package(args.negative_output,negative_items,
        'Actual certified two-cut hardware versus original native component under separately relaxed service bounds. All545 functional output bits, paired initial states, no continuing-state helper. Each counterexample validated with ABC testcex -a.')
    print(json.dumps({'local_files':len(local_manifest['files']),
        'local_bytes':local_manifest['total_bytes'],
        'negative_files':len(negative_manifest['files']),
        'negative_bytes':negative_manifest['total_bytes']},indent=2))


if __name__=='__main__':
    main()
