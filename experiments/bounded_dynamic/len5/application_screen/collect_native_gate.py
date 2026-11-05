#!/usr/bin/env python3
"""Package a completed source-bound native-arithmetic GLA diagnostic."""
import argparse
import gzip
import json
from pathlib import Path
import re

from collect_gate_solver import check_result
from gate_solver import digest, require
from native_gate_solver import validate_native


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--query', type=Path, required=True)
    parser.add_argument('--toys', type=Path, required=True)
    parser.add_argument('--source-audit', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    query = args.query.resolve()
    result = check_result(query)
    prepared = Path(result['prepared_directory'])
    model, dependencies = validate_native(prepared)
    require(result['abstraction_mode'] == 'none' and result['post_run_dependencies_verified'] is True,
            'Native query postcheck did not pass')
    require(result['prepared_summary_sha256'] == digest(prepared/'summary.json'), 'Preparation record changed')
    require(result['proof_dependencies_sha256'] == dependencies, 'Transitive proof closure changed')
    require(result['input_aig_sha256'] == model['aig_sha256'], 'Solved source model differs')
    for path, expected in result['wrapper_dependencies_sha256'].items():
        require(digest(Path(path)) == expected, 'Wrapper dependency changed')
    for path, expected in result['wrapper_artifacts_sha256'].items():
        require(digest(query/path) == expected, 'Wrapper snapshot changed')
    toys = args.toys.resolve()
    toy_summary = json.loads((toys/'summary.json').read_text())
    require(toy_summary['status'] == 'all_four_toys_passed', 'Solver qualification incomplete')
    require(toy_summary['gate_solver_sha256'] == result['script_sha256'], 'Toy and target engine drivers differ')
    for case in toy_summary['cases']:
        toy = check_result(toys/case['case']/'gla')
        require(toy['status'] == case['expected'], 'Toy result changed')
        require(digest(toys/case['case']/'gla/summary.json') == case['result_summary_sha256'], 'Toy record changed')
    audit = args.source_audit.resolve()
    source = json.loads((audit/'summary.json').read_text())
    require(source['installed_abc_sha256'] == result['execution']['executable_sha256'], 'Qualified ABC binary differs')
    output = args.output.resolve(); output.mkdir(parents=True, exist_ok=False)
    records = []
    def keep(path, relative):
        raw = path.read_bytes(); compressed = path.suffix == '.aig' or len(raw) > 100_000
        if compressed: relative += '.gz'
        dest = output/relative; dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(gzip.compress(raw, mtime=0) if compressed else raw)
        records.append(dict(path=relative, source=str(path), source_sha256=digest(path),
            sha256=digest(dest), gzip=compressed))
    for directory, prefix in ((query, 'query'), (toys, 'toys'), (audit, 'source_audit')):
        for path in sorted(directory.rglob('*')):
            if path.is_file(): keep(path, prefix+'/'+str(path.relative_to(directory)))
    keep(prepared/'summary.json', 'prepared_summary.json')
    keep(Path(__file__), 'collector_source.py')
    log = (query/'gla.log').read_text()
    timeout = re.search(r'GLA reached timeout (\d+) sec in frame (\d+) with a (\d+)-stable abstraction', log)
    calls = re.search(r'Concurrent calls = (\d+)', log)
    provenance = dict(status=result['status'], accepted_optimization=False,
        prepared_directory=str(prepared), prepared_summary_sha256=result['prepared_summary_sha256'],
        source_native_hardware_sha256=model['core_json_sha256'],
        query_model_sha256=model['query_core_sha256'], input_aig_sha256=result['input_aig_sha256'],
        native_arithmetic_retained=True, query_property_counts=result['query_property_counts'],
        proof_dependency_count=len(dependencies), requested_seconds=result['requested_seconds'],
        folded_header=result.get('folded_header'), abstracted_header=result.get('abstracted_header'),
        proof_thread_calls=int(calls[1]) if calls else None,
        timeout_frame=int(timeout[2]) if timeout else None,
        stable_frames_at_timeout=int(timeout[3]) if timeout else None,
        source_identity_caveat=source['source_identity_caveat'],
        scope=result['native_query_scope'],
        interpretation='All maps are proof-only overapproximations. Smaller maps, bounded progress, and timeouts '
            'are not unbounded certificates or hardware savings. Only the qualified engine terminal and status '
            'can establish proof; a SAT outcome additionally requires testcex against the original folded query.',
        artifacts=records)
    (output/'PROVENANCE.json').write_text(json.dumps(provenance, indent=2)+'\n')
    (output/'SHA256SUMS').write_text(''.join(f'{digest(path)}  {path.relative_to(output)}\n'
        for path in sorted(output.rglob('*')) if path.is_file()))
    print(json.dumps(dict(status=result['status'], artifacts=len(records),
        bytes=sum(path.stat().st_size for path in output.rglob('*') if path.is_file()))))


if __name__ == '__main__':
    main()
