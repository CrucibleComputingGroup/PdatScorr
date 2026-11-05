#!/usr/bin/env python3
"""Bounded GLA diagnostic on the closed, native-arithmetic admission query.

This separate entry point does not change gate_solver's ALU-abstraction CLI.
It reuses that qualified engine, constraint folding, and strict verdict/CEX
validation. The model retains native arithmetic and all original properties.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path

import gate_solver
import solve_prepared
from gate_solver import digest, require, run_gla
from solve_prepared import validate_prepared


def validate_native(directory):
    directory = Path(directory).resolve()
    model = validate_prepared(directory)
    require(model['abstraction_mode'] == 'none' and model['datapath_abstraction'] is None
            and model['abstraction_helper_sha256'] is None, 'Native arithmetic is required')
    require(model['query_property_counts'] == {'assert':3, 'assume':8, 'cover':0},
            'Original three assertions and eight assumptions are required')
    require(model['instruction_model'] == 'immutable_rom' and model['instruction_fault_payload'] == 'zero',
            'Exact immutable zero-fault ROM is required')
    require(model['native_hardware_contains_formal_properties'] is False,
            'Native hardware must remain separate from proof-only facts')
    require(model['certified_decoder_import']['status'] == 'certificate_replayed_and_native_substitution_bound',
            'Closed certified decoder is required')
    require(model['native_word_domain_import']['status'] == 'seven_proved_native_word_domains_imported'
            and model['external_rom_domain_import']['status'] == 'exact_external_rom_domain_certified',
            'Native word and external ROM closure are required')
    facts = model.get('inactive_fu_import')
    require(isinstance(facts, dict) and facts.get('status') == 'inactive_fu_reset_facts_replayed',
            'Closed inactive-FU reset facts are required')
    require(facts['query_only'] is True and facts['accepted_optimization'] is False
            and facts['native_hardware_export_unchanged'] is True and facts['assumptions_added'] == 0
            and facts['new_environmental_premises'] == [] and len(facts['reset_substitutions']) == 1761,
            'Inactive-FU composition scope changed')
    require(Path(model['query_core_path']).resolve() == directory/'inactive_query_core.json',
            'Final query must be the exact inactive-FU graph, without a subsequent payload cut')
    dependencies = {}
    for key in ('inactive_fu_import', 'native_word_domain_import', 'external_rom_domain_import'):
        for path, expected in model[key]['proof_dependencies_sha256'].items():
            require(path not in dependencies or dependencies[path] == expected, 'Conflicting proof dependency')
            dependencies[path] = expected
    require(all(model['native_word_domain_import']['proof_dependencies_sha256'].get(path) == expected
                for path, expected in facts['proof_dependencies_sha256'].items()),
            'Inactive-FU transitive dependencies are missing from the prepared solver closure')
    for path, expected in dependencies.items():
        require(digest(Path(path)) == expected, 'Proof dependency changed: '+path)
    return model, dependencies


def run_native(prepared, output, *, abc='/usr/local/bin/abc', timeout=600):
    require(0 < timeout <= 600, 'Budget must be positive and at most 600 seconds')
    prepared, output = Path(prepared).resolve(), Path(output).resolve()
    model, dependencies = validate_native(prepared)
    binding = digest(prepared/'summary.json')
    driver_paths = [Path(__file__), Path(gate_solver.__file__), Path(solve_prepared.__file__)]
    drivers = {str(path.resolve()): digest(path) for path in driver_paths}
    snapshots = {path.name: path.read_bytes() for path in driver_paths}
    record = run_gla(prepared/'screen.aig', output, abc=abc, timeout=timeout)
    record.update(prepared_directory=str(prepared), prepared_summary_sha256=binding,
        requested_seconds=timeout, query_property_counts=model['query_property_counts'],
        abstraction_mode='none', inactive_reset_substitutions=1761,
        proof_dependencies_sha256=dependencies, wrapper_dependencies_sha256=drivers,
        native_hardware_json_sha256=model['core_json_sha256'],
        query_model_sha256=model['query_core_sha256'],
        native_query_scope='Native arithmetic and original control retained after source-closed program-only reset facts. '
            'No added premise, state bound, tag restriction, or payload cut. A proof establishes only this safety query; '
            'a validated counterexample belongs to this formal ROM/memory platform and arbitrary-load/undefined-value domain, '
            'not automatically a concrete benchmark execution or hardware defect.')
    try:
        final_model, final_dependencies = validate_native(prepared)
        require(digest(prepared/'summary.json') == binding and final_dependencies == dependencies,
                'Preparation or proof dependency closure changed during GLA')
        require(final_model['aig_sha256'] == record['input_aig_sha256'], 'Solved AIG differs from preparation')
        for path, expected in drivers.items():
            require(digest(Path(path)) == expected, 'Solver wrapper dependency changed: '+path)
        record['post_run_dependencies_verified'] = True
    except (ValueError, OSError, KeyError) as error:
        record.update(status='error', error=str(error), post_run_dependencies_verified=False)
    for name, content in snapshots.items():
        dest = output/'wrapper_sources'/name
        dest.parent.mkdir(exist_ok=True)
        dest.write_bytes(content)
    record['wrapper_artifacts_sha256'] = {str(path.relative_to(output)): digest(path)
        for path in (output/'wrapper_sources').iterdir()}
    (output/'summary.json').write_text(json.dumps(record, indent=2)+'\n')
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepared', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--abc', default='/usr/local/bin/abc')
    parser.add_argument('--timeout', type=int, default=600)
    args = parser.parse_args()
    result = run_native(args.prepared, args.output, abc=args.abc, timeout=args.timeout)
    print(json.dumps({'status':result['status'], 'accepted_optimization':False}))


if __name__ == '__main__':
    main()
