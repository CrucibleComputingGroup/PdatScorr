#!/usr/bin/env python3
"""Replay cumulative RF certificate and audit theorem transfer; no solver."""
import argparse
import collections
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
APP = HERE.parents[1]
ISA = APP.parent / 'isa_baseline'
BUILD = Path('/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build')
spec = importlib.util.spec_from_file_location('independent_reset_audit', HERE.parent/'inactive_fu_import_v1/audit.py')
reset_audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reset_audit)
read, sha, require = reset_audit.read, reset_audit.sha, reset_audit.require


def output_bits(cells):
    return {bit for cell in cells for pin, direction in cell['port_directions'].items()
            if direction == 'output' for bit in cell['connections'][pin] if type(bit) is int}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--replay-directory', type=Path, required=True)
    args = parser.parse_args()
    replay = args.replay_directory.resolve()
    replay.mkdir(parents=True, exist_ok=False)
    certificate_path = ISA/'results/program_registers_certificate_v2.json'
    certificate = read(certificate_path)
    decoder_path = Path(certificate['decoder_certificate'])
    decoder_certificate = read(decoder_path)
    native_path = Path(certificate['native_original_json'])
    decoder_candidate_path = Path(decoder_certificate['native_candidate_json'])
    cumulative_path = Path(certificate['native_candidate_json'])
    require(sha(ISA/'certify_registers.py') == certificate['certifier_sha256'], 'RF certifier changed')
    require(sha(decoder_path) == certificate['decoder_certificate_sha256'], 'Parent decoder certificate changed')
    require(sha(cumulative_path) == certificate['native_candidate_sha256'], 'Cumulative candidate changed')
    require(sha(decoder_candidate_path) == decoder_certificate['native_candidate_sha256'], 'Parent candidate changed')
    require(sha(native_path) == certificate['native_original_sha256'], 'Original core changed')
    dependencies = {str(path): sha(path) for path in [Path(__file__), Path(reset_audit.__file__),
        certificate_path, decoder_path, native_path, decoder_candidate_path, cumulative_path,
        ISA/'certify_registers.py', ISA/'certify.py', ISA/'lower_demux.py', APP.parents[3]/'odc/temporal.py']}
    dirs = ['register_baseline_prepare_v1', 'register_baseline_prepare_v2', 'program_registers_v2',
            'rd_domain_symbolic_v5', 'register_pair_symbolic_v1', 'register_lowering_symbolic_v2']
    for directory in dirs:
        for path in (BUILD/directory).rglob('*'):
            if path.is_file():
                dependencies[str(path)] = sha(path)
    for key in ('evidence_summary_sha256', 'proof_log_sha256'):
        for path, value in certificate[key].items():
            require(dependencies[path] == value, 'Archived certificate dependency changed')
    prepared = BUILD/'harvard_rom_inactive_fu_native_prepare_v1'
    facts = read(prepared/'summary.json')
    for record in ('native_word_domain_import', 'external_rom_domain_import', 'inactive_fu_import'):
        for path, value in facts[record]['proof_dependencies_sha256'].items():
            require(dependencies.get(path, value) == value, 'Conflicting prior theorem binding')
            dependencies[path] = value
    reset_audit.verify(dependencies)
    command = [sys.executable, str(ISA/'certify_registers.py'), '--decoder-certificate', str(decoder_path),
        '--original-rf', str(BUILD/'register_baseline_prepare_v1/decoder.json'),
        '--prepared-rf', str(BUILD/'register_baseline_prepare_v2'), '--candidate', str(BUILD/'program_registers_v2'),
        '--domain-proof', str(BUILD/'rd_domain_symbolic_v5'), '--pair-recheck', str(BUILD/'register_pair_symbolic_v1'),
        '--lowering-proof', str(BUILD/'register_lowering_symbolic_v2'), '--output', str(replay/'certificate.json')]
    start = time.monotonic()
    execution = subprocess.run(command, capture_output=True, text=True, timeout=30)
    (replay/'replay.log').write_text(execution.stdout + execution.stderr)
    require(execution.returncode == 0, 'Certificate replay failed: ' + execution.stderr)
    require(read(replay/'certificate.json') == certificate, 'Fresh cumulative certificate differs')
    native = read(native_path)['modules']['datapath']
    decoder = read(decoder_candidate_path)
    cumulative = read(cumulative_path)
    a, b = decoder['modules']['datapath'], cumulative['modules']['datapath']
    removed, added = set(a['cells'])-set(b['cells']), set(b['cells'])-set(a['cells'])
    changed = {name for name in set(a['cells']) & set(b['cells']) if a['cells'][name] != b['cells'][name]}
    require(removed == {'$1760'} and len(added) == 64 and not changed, 'Unexpected RF specialization delta')
    types = dict(collections.Counter(b['cells'][name]['type'] for name in added))
    require(types == {'$mux': 32, '$eq': 7, '$pos': 25}, 'Unexpected RF decode structure')
    for key in set(a) | set(b):
        if key != 'cells':
            require(a.get(key) == b.get(key), 'RF specialization changed module metadata/aliases/ports')
    rf = read(BUILD/'register_baseline_prepare_v1/decoder.json')['modules']['DecoderBase']
    require(len(rf['cells']) == 55, 'RF source component changed')
    require(all(cell == native['cells'][name] == a['cells'][name] for name, cell in rf['cells'].items()), 'Native RF component binding changed')
    drivers = output_bits(rf['cells'].values())
    observed = {bit for port in rf['ports'].values() if port['direction'] == 'output' for bit in port['bits']}
    leaks = [(name, pin, bit) for name, cell in native['cells'].items() if name not in rf['cells']
             for pin, direction in cell['port_directions'].items() if direction == 'input'
             for bit in set(cell['connections'][pin]) & drivers - observed]
    leaks += [(name, 'top_output', bit) for name, port in native['ports'].items() if port['direction'] == 'output'
              for bit in set(port['bits']) & drivers - observed]
    require(len(observed) == 128 and not leaks, 'Unobserved external RF consumer')
    prefix = 'u_backend.u_exec_stage.u_alu_unit.u_arith_rs.'
    aliases = {name: list(a['netnames'][prefix+name]['bits']) for name in ('insert', 'new_idx', 'data', 'curr_state')}
    require(all(b['netnames'][prefix+name]['bits'] == bits for name, bits in aliases.items()), 'Admission/state aliases changed')
    alias_bits = {bit for bits in aliases.values() for bit in bits}
    target_drivers = {name for name, cell in a['cells'].items() if output_bits([cell]) & alias_bits}
    require(all(a['cells'][name] == b['cells'][name] for name in target_drivers), 'Native ALU admission/state driver changed')
    substitutions = {int(bit): value for bit, value in facts['inactive_fu_import']['reset_substitutions'].items()}
    reset_then_rf, _, _ = reset_audit.graph_rewrite(decoder, substitutions)
    for name in removed:
        del reset_then_rf['modules']['datapath']['cells'][name]
    for name in added:
        reset_then_rf['modules']['datapath']['cells'][name] = copy.deepcopy(b['cells'][name])
    rf_then_reset, _, _ = reset_audit.graph_rewrite(cumulative, substitutions)
    require(reset_then_rf == rf_then_reset, 'RF and reset-fact substitutions do not commute')
    word = facts['native_word_domain_import']
    protected = set(word['source_projection_data_cells']) | set(word['source_projection_preserved_control_cells'])
    require(len(protected) == 57 and all(a['cells'][name] == b['cells'][name] for name in protected), 'Word theorem projection changed')
    lemma = read(prepared/'lemma_core.json')['modules']['datapath']
    collisions = sorted(output_bits(b['cells'][name] for name in added) & output_bits(lemma['cells'][name] for name in word['added_cells']))
    require(collisions == list(range(230483, 230515)), 'Wire allocation collision changed')
    rd_cells = set(certificate['domain_projection_retained_control_cells']) | set(certificate['domain_projection_retained_data_cells'])
    changed_after_reset = sorted(name for name in rd_cells if b['cells'][name] != rf_then_reset['modules']['datapath']['cells'].get(name))
    require(len(rd_cells) == 381 and len(changed_after_reset) == 10, 'Unexpected RD-projection overlap with later reset facts')
    for path in (prepared/'summary.json', prepared/'lemma_core.json', prepared/'inactive_query_core.json',
                 HERE.parent/'inactive_fu_native_v1/summary.json', HERE.parent/'inactive_fu_import_v1/summary.json'):
        dependencies[str(path)] = sha(path)
    reset_audit.verify(dependencies)
    replay_record = {'argv': command, 'returncode': execution.returncode, 'seconds': time.monotonic()-start,
                     'log_sha256': sha(replay/'replay.log'), 'fresh_certificate_sha256': sha(replay/'certificate.json'),
                     'certificate_equal_to_archive': True, 'new_solver_queries': 0}
    for name in ('certificate.json', 'replay.log'):
        (HERE/name).write_bytes((replay/name).read_bytes())
    result = {'status': 'cumulative_rf_certificate_and_admission_transfer_review_passed',
              'new_solver_queries': 0, 'native_candidate_sha256': certificate['native_candidate_sha256'],
              'certificate_replay': replay_record, 'source_sha256': dependencies,
              'rf_delta': {'removed': sorted(removed), 'added_cells': 64, 'added_types': types,
                           'changed_retained_cells': 0, 'ff_cells_before_cleanup': 1228,
                           'capacities_ports_aliases_unchanged': True},
              'original_rf_cells': 55, 'observed_read_output_bits': 128, 'unobserved_external_consumers': leaks,
              'outside_rf_alu_admission_and_state_aliases': {name: len(bits) for name, bits in aliases.items()},
              'unchanged_admission_and_state_driver_cells': sorted(target_drivers),
              'reset_rewrite_commutes_exactly': True, 'word_projection_cells_unchanged': 57,
              'old_predicate_output_bit_collisions': collisions, 'rd_projection_cells_changed_by_later_reset_substitution': changed_after_reset,
              'transfer_conclusion': 'A source-closed admission theorem on the decoder-only native core transfers to the exact cumulative RF candidate under the same initial reset and external instruction/memory contract: RF equivalence observes every external RF consumer and preserves all outside-RF state, including ALU-RS rows, and the unchanged ALU admission predicate. No new whole-core equivalence-engine run is needed for this compositional transfer.',
              'required_conditions': ['An actual unbounded admission theorem must first exist for the exact native or soundly overapproximated query; this review does not supply it.',
                  'Use exact cumulative candidate 371a91db44e992635c234ba339907654b62a6800c43d787561cea2bbbbe67b7e and replay both certificates with all transitive source/model/log hashes and Python assertions enabled.',
                  'Retain the identical reset, immutable zero-fault ROM, and external service domain; RF proof needs no new timing or capacity premise.',
                  'The eventual physical RS edit must independently follow from the admission theorem plus closed row/reset and consumer-observation reasoning; an admission bound alone is not a hardware-equivalence proof.',
                  'Apply the certified RF native baseline before physical RS edits and report their increment against this same baseline. Keep query-only lemmas and any arithmetic abstraction out of physical hardware.',
                  'If accelerating queries with the RF candidate, import RF equivalence before reset rewrites, regenerate seven word predicates with fresh wire IDs, and explicitly rebind the unchanged extracted ROM producer/port boundary to the new native descriptor hash.'],
              'limitations': ['The certificate is a compositional outside-component equivalence proof, not a full-core engine run.',
                  'Structural graph counts are not mapped area or savings.',
                  'No live source, query, or dependency was edited; the only subprocess replayed the existing certifier into a fresh directory.']}
    (HERE/'summary.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'status': result['status'], 'fresh_certificate_equal': True, 'read_output_bits': 128,
                      'rf_reset_commute': True, 'predicate_bit_collisions': len(collisions), 'new_solver_queries': 0}))


if __name__ == '__main__':
    main()
