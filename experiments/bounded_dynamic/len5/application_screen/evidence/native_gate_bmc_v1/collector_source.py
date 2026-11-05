#!/usr/bin/env python3
"""Package one source-bound bounded native-map diagnostic without rerunning it."""
import argparse
import gzip
import json
from pathlib import Path
import re

from gate_bmc import digest, require, verdict
from native_gate_bmc import check_dependencies, validate_native_gla


def read(path): return json.loads(path.read_text())


def check_bmc(directory, record):
    for name, expected in record['artifact_sha256'].items():
        require(digest(directory/name) == expected, 'BMC artifact changed')
    require(digest(Path(record['input_aig'])) == record['input_sha256'], 'BMC input changed')
    raw = verdict(record['execution'], (directory/'bmc.log').read_text(), record['raw_status'], record['requested_frames'])
    if record['status'] == 'counterexample_in_abstraction_only':
        require(raw == 'counterexample_pending_validation', 'Missing strict counterexample verdict')
        require(re.search(r'And\s+AIG: The cex is correct\.', (directory/'validate_cex.log').read_text()),
                'Counterexample was not validated against the exact abstraction')
        require((directory/'counterexample.aiw').is_file(), 'Counterexample trace is missing')
    else:
        require(raw == record['status'], 'Bounded verdict changed')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', type=Path, required=True)
    parser.add_argument('--toys', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    run, toys = args.run.resolve(), args.toys.resolve()
    record = read(run/'summary.json')
    require(record['accepted_optimization'] is False and record['unbounded_certificate'] is False
            and record['post_run_dependencies_verified'] is True, 'Unexpected acceptance or failed postcheck')
    gla = Path(record['gla_result_directory'])
    info, native, _ = validate_native_gla(gla)
    check_dependencies(record['source_dependencies_sha256'])
    check_bmc(run/'bmc', record)
    for name, expected in record['wrapper_artifacts_sha256'].items():
        require(digest(run/name) == expected, 'Wrapper snapshot changed')
    replay = record['gate_map_replay']
    require(digest(run/'map_replay/rederived.aig') == record['input_sha256'] == replay['abstracted_sha256']
            == replay['rederived_sha256'] == digest(gla/'abstracted.aig'), 'Exact map replay differs')
    cases = []
    for index, expected in ((0,'bounded_only_no_certificate'), (1,'counterexample_in_abstraction_only')):
        path = toys/f'test_real_bounded_positive_and{index}'
        toy = read(path/'bmc/summary.json'); check_bmc(path/'bmc', toy)
        require(toy['status'] == expected and toy['script_sha256'] == record['script_sha256'],
                'Qualified toy outcome or BMC source differs')
        require(toy['execution']['executable_sha256'] == record['execution']['executable_sha256'],
                'Qualified ABC binary differs')
        cases.append(dict(directory=str(path), status=expected, summary_sha256=digest(path/'bmc/summary.json')))
    out = args.output.resolve(); out.mkdir(parents=True, exist_ok=False); files = []
    def keep(path, relative):
        raw = path.read_bytes(); compressed = path.suffix == '.aig' or len(raw) > 100000
        if compressed: relative += '.gz'
        dest = out/relative; dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(gzip.compress(raw, mtime=0) if compressed else raw)
        files.append(dict(path=relative, sha256=digest(dest), source=str(path), source_sha256=digest(path), gzip=compressed))
    for directory, prefix in ((run,'query'), (toys,'toys')):
        for path in sorted(directory.rglob('*')):
            if path.is_file(): keep(path, prefix+'/'+str(path.relative_to(directory)))
    prepared = Path(record['source_prepared_directory'])
    keep(prepared/'summary.json', 'source_prepared_summary.json')
    keep(gla/'summary.json', 'source_gla_summary.json')
    keep(Path(__file__), 'collector_source.py')
    root = Path(__file__).resolve().parents[4]
    for name in ('test_gate_bmc.py','test_native_gate_bmc.py'):
        keep(root/'tests/unit'/name, name)
    provenance = dict(status=record['status'], accepted_optimization=False, unbounded_certificate=False,
        counterexample_frame=record.get('counterexample_frame'),
        reported_no_counterexample_frames=record['reported_no_counterexample_frames'],
        requested_frames=record['requested_frames'], requested_seconds=record['requested_seconds'],
        actual_solver_seconds=record['execution']['seconds'], input_header=record['input_header'],
        input_sha256=record['input_sha256'], exact_map_replay=True,
        all_source_dependencies_revalidated=True, source_dependency_count=len(record['source_dependencies_sha256']),
        native_hardware_sha256=native['core_json_sha256'], native_source_query_arithmetic_retained=True,
        toy_outcomes=cases, source_gate_map=dict(sha256=replay['map_sha256'], original_path=replay['map_path'],
            existing_compact_copy='../native_gate_solver_v1/query/final_map.aig.gz'),
        interpretation='Bounded diagnostic of an overapproximation only. A validated counterexample is not a native '
            'execution until concretized; bounded absence is not an unbounded certificate. No PDR or refinement follows automatically.',
        artifacts=files)
    (out/'PROVENANCE.json').write_text(json.dumps(provenance, indent=2)+'\n')
    (out/'SHA256SUMS').write_text(''.join(f'{digest(path)}  {path.relative_to(out)}\n'
        for path in sorted(out.rglob('*')) if path.is_file()))
    print(json.dumps(dict(status=record['status'], files=len(files),
        bytes=sum(path.stat().st_size for path in out.rglob('*') if path.is_file()))))


if __name__ == '__main__':
    main()
