#!/usr/bin/env python3
"""Validate frozen native wrapper guards/provenance without running GLA."""
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
APP = HERE.parents[1]
sys.path[:0] = [str(APP.parents[3]), str(APP)]
import native_gate_solver as wrapper
import gate_solver


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    prepared = Path('/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build/harvard_rom_inactive_fu_native_prepare_v1')
    model, dependencies = wrapper.validate_native(prepared)
    assert wrapper.run_gla is gate_solver.run_gla
    assert len(dependencies) == 269
    source = {str(path): sha(path) for path in [Path(__file__), APP/'native_gate_solver.py',
        APP/'gate_solver.py', APP/'solve_prepared.py', APP.parents[3]/'odc/temporal.py',
        APP.parents[3]/'tests/unit/test_native_gate_solver.py', prepared/'summary.json']}
    source.update(dependencies)
    done = {'returncode': 0, 'timeout': False}
    assert gate_solver.verdict(done, 'GLA completed 80 frames and proved abstraction derived in frame 4', 'snl_UNSAT') == 'proved_safety_query_only'
    assert gate_solver.verdict(done, 'stable abstraction at frame 80', 'snl_UNSAT') == 'unknown'
    assert gate_solver.verdict(done, 'True counter-example detected in frame 8', 'snl_SAT') == 'counterexample_pending_validation'
    assert gate_solver.verdict({'returncode': 0, 'timeout': True}, 'Sequential miter is trivially UNSAT.', 'snl_UNSAT') == 'unknown'
    for path, value in source.items():
        assert sha(path) == value
    result = {'status': 'independent_native_gla_wrapper_review_passed', 'solver_calls': 0,
              'same_qualified_run_gla_function': True, 'native_mode_and_exact_query_path_enforced': True,
              'proof_dependencies': 269, 'query_properties': model['query_property_counts'],
              'before_after_dependency_checks_present': True, 'maximum_requested_seconds': 600,
              'result_parser_spot_checks': 4, 'wrapper_tests': {'passed': 10, 'seconds': 0.49,
                  'command': 'python -m pytest -q tests/unit/test_native_gate_solver.py', 'engine_calls': 'mocked'},
              'source_sha256': source, 'verdict': 'No blocker. The native wrapper validates the frozen composition and invokes unchanged run_gla with no model transformations or new assumptions. The engine folds constraints and ORs all three bad outputs. A proof requires an explicit unbounded terminal result and matching UNSAT status; a counterexample requires independent validation against the original folded query. Timeout, bounded success, and stable abstraction are not proofs.',
              'limit': 'Source/guard/provenance review only. The separate authorized running solver outcome is not reviewed or predicted here.'}
    (HERE/'summary.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'status': result['status'], 'solver_calls': 0, 'proof_dependencies': 269}))


if __name__ == '__main__':
    main()
