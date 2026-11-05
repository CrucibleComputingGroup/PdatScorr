#!/usr/bin/env python3
"""Retain guard/protocol attempts with exact models and no success inflation."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    workspace = next(p for p in HERE.parents if (p/'tools/oss-cad-suite-20261104').exists())
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--build', type=Path, default=workspace/'experiments/bounded_dynamic/len5/phase_sharing/build')
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True)
    records = []
    def retain(src, name, compress=False):
        dst = out/name
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_bytes(gzip.compress(src.read_bytes(), mtime=0) if compress else src.read_bytes())
        records.append({'path':name,'sha256':sha(dst),'source':str(src.resolve()),
                        'source_sha256':sha(src),'gzip':compress})
    jobs = ['guards_v1','guards_v2','conditional_tags_v1','native_duplicate_tag_falsifier_v1']
    outcomes = {}
    for job in jobs:
        source = args.build/job
        outcomes[job] = json.loads((source/'summary.json').read_text())
        for path in sorted(source.rglob('*')):
            if not path.is_file():
                continue
            rel = str(path.relative_to(args.build))
            if path.suffix in ('.log','.sv','.ys','.py') or path.name in ('summary.json','discovery.json','manifest.json'):
                compress = path.stat().st_size > 100_000
                retain(path, rel+('.gz' if compress else ''), compress)
            elif path.suffix == '.vcd':
                retain(path, rel+'.gz', True)
            elif path.name == 'model.aig':
                retain(path, rel)
            elif job == 'conditional_tags_v1' and path.parent.name == 'negative_protocol' and path.name == 'model.smt2':
                retain(path, rel+'.gz', True)
    source = args.build/'native_candidate_v1/coherent_candidate'
    retain(source/'native.json','source_model/native.json.gz',True)
    retain(source/'proof.json','source_model/proof.json')
    for name in ('guard_invariants.py','conditional_protocol.py','guard_protocol_review.md'):
        retain(HERE/name,'current_sources/'+name)
    root = HERE.parents[3]
    retain(root/'tests/unit/test_guard_invariants.py','current_sources/test_guard_invariants.py')
    raw = args.build/'native_duplicate_tag_falsifier_v1/manifest.json'
    bindings = json.loads(raw.read_text())
    prior = HERE/'results/phase_control_v1/native'
    assert sha(prior/'reference.v') == bindings['sha256']['reference']
    assert sha(prior/'unaccepted_candidate.v') == bindings['sha256']['candidate']
    source_paths = [
        'rtl/common/rr_arbiter.sv','rtl/expipe/exec-units/arith_rs.sv',
        'rtl/expipe/issue-unit/issue_stage.sv','rtl/expipe/issue-unit/issue_cu.sv',
        'rtl/expipe/commit-unit/rob.sv','rtl/expipe/commit-unit/commit_stage.sv',
        'rtl/packages/expipe_pkg.sv','rtl/expipe/backend.sv',
    ]
    snapshot = workspace/'experiments/bounded_dynamic/len5/build/pre_fpu_simulation/source'
    for name in source_paths:
        retain(snapshot/name,'source_review/'+name)
    summary = {
        'status':'no_target_candidate_proven', 'accepted_rewrites':0,
        'physical_mapping_performed':False,
        'purpose':'Automatic guarded representation discovery; conditional tag protocol is intermediate only',
        'source_commit':'14291dcc5bef181085d001c5a29e7f4fc4cbc8e9',
        'guard_candidates':outcomes['guards_v1']['candidate_count'],
        'guard_rejected':len(outcomes['guards_v1']['screen']['rejected']),
        'guard_survivors':len(outcomes['guards_v1']['screen']['survivors']),
        'guard_joint_proven':outcomes['guards_v2']['proven'],
        'conditional_proven':outcomes['conditional_tags_v1']['conditional_proven'],
        'conditional_assumptions_total':outcomes['conditional_tags_v1']['joint']['property_counts']['assume'],
        'native_allocator_protocol_closure_proved':False,
        'explicit_negative_protocol_counterexample':outcomes['conditional_tags_v1']['negative_protocol']['explicit_assertion_counterexample'],
        'native_simulation':outcomes['native_duplicate_tag_falsifier_v1'],
        'native_pair_reference':{'directory':'../phase_control_v1/native',
            'reference_sha256':bindings['sha256']['reference'],
            'unaccepted_candidate_sha256':bindings['sha256']['candidate']},
        'interpretation':'No target proof or hardware savings established. Failed induction is not a reachable counterexample. Monitor negative validates protocol rejection only. Native simulation has no mismatch and is inconclusive.',
        'artifacts':records,
    }
    (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({'files':len(records),'bytes':sum(p.stat().st_size for p in out.rglob('*') if p.is_file()),'status':summary['status']}))


if __name__ == '__main__':
    main()
