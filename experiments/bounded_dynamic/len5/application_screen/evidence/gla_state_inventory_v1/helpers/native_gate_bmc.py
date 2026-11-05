#!/usr/bin/env python3
"""One bounded search on the exact saved native-query GLA abstraction."""
from __future__ import annotations
import argparse
import json
from pathlib import Path

import gate_bmc
import gate_pdr
import gate_solver
import native_gate_solver
import solve_prepared
from gate_bmc import run_bmc
from gate_pdr import rederive_map
from gate_solver import digest, header, require, verdict
from native_gate_solver import validate_native


def check_dependencies(dependencies):
    for path, expected in dependencies.items():
        require(digest(Path(path)) == expected, 'Native GLA dependency changed: '+path)


def validate_native_gla(directory):
    directory = Path(directory).resolve()
    info = json.loads((directory/'summary.json').read_text())
    prepared = Path(info['prepared_directory']).resolve()
    model, dependencies = validate_native(prepared)
    dependencies = dict(dependencies)
    def bind(path, expected):
        path = str(Path(path).resolve())
        require(path not in dependencies or dependencies[path] == expected, 'Conflicting source binding')
        dependencies[path] = expected
    bind(directory/'summary.json', digest(directory/'summary.json'))
    bind(prepared/'summary.json', info['prepared_summary_sha256'])
    require(info['status'] == 'unknown' and info['accepted_optimization'] is False
            and info['post_run_dependencies_verified'] is True and info['abstraction_mode'] == 'none',
            'Only the unresolved, validated native GLA result is eligible')
    require(info['proof_dependencies_sha256'] == dependencies_subset(model), 'GLA theorem closure differs')
    require(info['input_aig_sha256'] == model['aig_sha256'] == digest(Path(info['input_aig'])),
            'GLA source AIG differs from prepared model')
    bind(Path(info['input_aig']), info['input_aig_sha256'])
    require(info['native_hardware_json_sha256'] == model['core_json_sha256']
            and info['query_model_sha256'] == model['query_core_sha256'], 'GLA native/query binding differs')
    require(info['query_property_counts'] == model['query_property_counts'], 'GLA property inventory differs')
    require(verdict(info['execution'], (directory/'gla.log').read_text(), info['raw_status']) == 'unknown',
            'Recorded GLA outcome differs from the strict engine verdict')
    for key in ('artifacts_sha256', 'wrapper_artifacts_sha256'):
        for name, expected in info[key].items():
            bind(directory/name, expected)
    for path, expected in info['wrapper_dependencies_sha256'].items():
        bind(path, expected)
    require(info['derive']['returncode'] == 0 and not info['derive']['timeout'], 'Map derivation failed')
    require((directory/'final_map.aig').is_file(), 'Exact final native GLA map is required')
    values = header(directory/'abstracted.aig')
    require(values == info['abstracted_header'], 'Derived abstraction header changed')
    require(int(values[4]) == 1 and all(int(value) == 0 for value in values[6:]),
            'Expected an already folded one-output map without constraint sections')
    check_dependencies(dependencies)
    return info, model, dependencies


def dependencies_subset(model):
    result = {}
    for key in ('inactive_fu_import', 'native_word_domain_import', 'external_rom_domain_import'):
        for path, expected in model[key]['proof_dependencies_sha256'].items():
            require(path not in result or result[path] == expected, 'Conflicting theorem dependency')
            result[path] = expected
    return result


def run_native_bmc(gla, output, *, frames=128, timeout=120, abc='/usr/local/bin/abc'):
    require(0 < frames <= 128 and 0 < timeout <= 120, 'Diagnostic budget exceeds authorized bound')
    gla, output = Path(gla).resolve(), Path(output).resolve()
    info, model, dependencies = validate_native_gla(gla)
    require(digest(Path(abc)) == info['execution']['executable_sha256'], 'Qualified ABC binary changed')
    sources = [Path(__file__), Path(gate_bmc.__file__), Path(gate_pdr.__file__),
        Path(gate_solver.__file__), Path(native_gate_solver.__file__), Path(solve_prepared.__file__)]
    snapshots = {path.name:path.read_bytes() for path in sources}
    for path in sources:
        dependencies[str(path.resolve())] = digest(path)
    output.mkdir(parents=True, exist_ok=False)
    replay = rederive_map(gla/'final_map.aig', gla/'abstracted.aig', output/'map_replay', abc=abc)
    validate_native_gla(gla)
    check_dependencies(dependencies)
    result = run_bmc(gla/'abstracted.aig', output/'bmc', frames=frames, timeout=timeout, abc=abc)
    result.update(gate_map_replay=replay, source_dependencies_sha256=dependencies,
        source_prepared_directory=info['prepared_directory'], gla_result_directory=str(gla),
        native_hardware_json_sha256=model['core_json_sha256'], native_arithmetic_in_source_query=True,
        source_query_property_counts=model['query_property_counts'],
        scope='Direct bounded diagnostic of the source-bound native-query GLA overapproximation. '
            'No refolding, added premise, or native hardware change. Any validated counterexample is abstraction-only; '
            'bounded absence is not an unbounded certificate. No automatic PDR follows.')
    try:
        validate_native_gla(gla)
        check_dependencies(dependencies)
        result['post_run_dependencies_verified'] = True
    except (ValueError, OSError, KeyError) as error:
        result.update(status='error', error=str(error), post_run_dependencies_verified=False)
    for name, content in snapshots.items():
        dest = output/'wrapper_sources'/name
        dest.parent.mkdir(exist_ok=True)
        dest.write_bytes(content)
    result['wrapper_artifacts_sha256'] = {str(path.relative_to(output)):digest(path)
        for path in (output/'wrapper_sources').iterdir()}
    (output/'summary.json').write_text(json.dumps(result, indent=2)+'\n')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--gla-result', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--frames', type=int, default=128)
    parser.add_argument('--timeout', type=int, default=120)
    parser.add_argument('--abc', default='/usr/local/bin/abc')
    args = parser.parse_args()
    result = run_native_bmc(args.gla_result, args.output, frames=args.frames, timeout=args.timeout, abc=args.abc)
    print(json.dumps({'status':result['status'], 'counterexample_frame':result.get('counterexample_frame'),
        'reported_frames':result['reported_no_counterexample_frames'], 'accepted_optimization':False}))


if __name__ == '__main__':
    main()
