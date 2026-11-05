#!/usr/bin/env python3
"""Bind decoder equivalence, native consumer closure, and domain propagation."""
import argparse
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[3]))
from odc.temporal import digest, proof_passed


def checked_pair(directory, candidate_directory):
    """Only a fresh source-bound safe-backend proof can authorize this certificate."""
    record = json.loads((directory/'summary.json').read_text())
    proof = record['proof']
    assert record['status'] == 'proved' and proof['proven']
    assert record['independent_undefined_choices'] and not record['assumptions_or_observations_changed']
    assert proof['undefined_value_model'].startswith('Independent symbolic choices before process optimization')
    assert digest(directory/'temporal_source.py') == proof['implementation_sha256']
    assert digest(directory/'recheck_source.py') == record['script_sha256']
    assert digest(candidate_directory/'summary.json') == record['candidate_summary_sha256']
    assert digest(candidate_directory/'candidate_whole_core.json') == record['native_candidate_sha256']
    for name in ('reference', 'candidate', 'harness'):
        suffix = '.sv' if name == 'harness' else '.v'
        assert digest(candidate_directory/(name+suffix)) == proof[name+'_sha256']
    pdr = proof['pdr']; log = Path(pdr['log'])
    assert pdr['returncode'] == 0 and not pdr['timeout'] and digest(log) == pdr['log_sha256']
    assert log.read_text().count('Property proved.') == 1
    assert digest(directory/'proof/miter.aig') == proof['aig_sha256']
    assert json.loads((directory/'proof/proof.json').read_text()) == proof
    return record


def checked_domain(directory):
    proof = json.loads((directory/'summary.json').read_text())
    assert proof['status'] == 'proved' and proof_passed(proof['base']) and proof_passed(proof['induction'])
    assert proof['undefined_semantics'].startswith('Native JSON primitive mapping then setundef-anyseq BEFORE prep/opt')
    assert digest(directory/'symbolized_before_prep.json') == proof['symbolized_before_prep_sha256']
    assert digest(directory/'prove_domain_source.py') == proof['source_sha256']
    assert digest(directory/'harness.sv') == proof['harness_sha256']
    assert proof['projection']['internal_assumptions_added'] == 0
    assert proof['external_word_premise_guard'] == 'rst_ni && instr_rvalid_i'
    for name in ('base', 'induction'):
        assert digest(Path(proof[name]['log'])) == proof[name]['log_sha256']
    # Despite its historical name this field contains every preserved control
    # combinational cell, including ROB masks in the destination-register proof.
    retained = set(proof['projection']['original_cell_slices']) | set(proof['projection']['retained_spill_write_control_cells'])
    return proof, retained


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepared', type=Path, required=True)
    parser.add_argument('--candidate', type=Path, required=True)
    parser.add_argument('--domain-proof', type=Path, required=True)
    parser.add_argument('--pair-recheck', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    assert not args.output.exists()
    prepared = json.loads((args.prepared/'manifest.json').read_text())
    proof, retained = checked_domain(args.domain_proof)
    recheck = checked_pair(args.pair_recheck, args.candidate)
    candidate = json.loads((args.candidate/'summary.json').read_text())
    assert candidate['status'] == 'decoder_equivalence_proved_native_candidate_emitted'
    assert proof['domain'] == candidate['domain']
    if 'target_net' in proof['projection']:
        assert proof['projection']['target_net'] == 'u_backend.u_issue_stage.u_issue_decoder.instruction_i'
    original_path = args.prepared/'whole_core.json'
    candidate_path = args.candidate/'candidate_whole_core.json'
    assert digest(original_path) == prepared['whole_core_json_sha256'] == proof['original_whole_core_sha256']
    assert digest(candidate_path) == candidate['candidate_whole_core_sha256']
    original = json.loads(original_path.read_text())['modules']['datapath']
    modified = json.loads(candidate_path.read_text())['modules']['datapath']
    decoder = json.loads((args.prepared/'decoder.json').read_text())['modules']['DecoderBase']
    projected = json.loads((args.domain_proof/'data_path.json').read_text())['modules']['InstructionDataPath']
    assert projected['ports']['decoder_word']['bits'] == decoder['ports']['instruction_i']['bits']
    assert projected['ports']['instruction_i']['bits'] == original['ports']['instr_rdata_i']['bits']
    assert projected['ports']['response_valid']['bits'] == original['ports']['instr_rvalid_i']['bits']
    assert digest(args.domain_proof/'harness.sv') == proof['harness_sha256']
    assert original['ports'] == modified['ports'] and original['netnames'] == modified['netnames']
    changed = {name for name, cell in original['cells'].items() if cell != modified['cells'][name]}
    assert changed == {item['cell'] for item in candidate['accepted']}
    assert changed <= decoder['cells'].keys() and set(original['cells']) == set(modified['cells'])
    component_drivers = {bit for cell in decoder['cells'].values() for port, direction in cell['port_directions'].items()
                         if direction == 'output' for bit in cell['connections'][port] if isinstance(bit, int)}
    observed = {bit for port in decoder['ports'].values() if port['direction'] == 'output' for bit in port['bits']}
    leaks = []
    for name, cell in original['cells'].items():
        if name in decoder['cells']:
            continue
        for port, direction in cell['port_directions'].items():
            if direction == 'input':
                for bit in set(cell['connections'][port]) & component_drivers - observed:
                    leaks.append({'consumer': name, 'port': port, 'bit': bit})
    for name, port in original['ports'].items():
        if port['direction'] == 'output':
            leaks += [{'top_output': name, 'bit': bit} for bit in set(port['bits']) & component_drivers - observed]
    assert not leaks
    assert not changed & retained
    assert not any(cell['type'] in ('$assume', '$assert', '$check', '$cover', '$anyseq', '$anyconst') for cell in modified['cells'].values())
    logs = [proof['base']['log'], proof['induction']['log'], recheck['proof']['pdr']['log']]
    record = {
        'status': 'component_equivalence_and_domain_propagation_certified',
        'scope': 'Compositional whole-core transfer under initial native reset and declared domain on valid instruction responses; no claim exact program ROM necessarily meets that domain',
        'external_premises': ['initial rst_ni == 0', '(rst_ni && instr_rvalid_i) -> instruction response word in declared domain'],
        'instruction_payload_during_reset_restricted': False,
        'timing_or_occupancy_premises': [], 'invalid_instruction_payload_restricted': False,
        'domain': candidate['domain'], 'domain_expression': candidate['domain_expression'],
        'native_original_json': str(original_path.resolve()), 'native_original_sha256': digest(original_path),
        'native_candidate_json': str(candidate_path.resolve()), 'native_candidate_sha256': digest(candidate_path),
        'decoder_outputs': prepared['observed_decoder_outputs'], 'all_decoder_external_consumers_observed': True,
        'unobserved_external_consumers': leaks, 'native_ports_and_all_unmodified_cells_preserved': True,
        'changed_cells': sorted(changed), 'original_state_cell_drivers_replaced': 0,
        'domain_projection_cells_unchanged_by_specialization': True,
        'domain_projection_retained_control_cells': sorted(set(proof['projection']['retained_spill_write_control_cells'])),
        'domain_projection_retained_data_cells': sorted(set(proof['projection']['original_cell_slices'])),
        'domain_undefined_semantics': proof['undefined_semantics'],
        'domain_symbolic_undefined_bits_before_prep': proof['symbolic_undefined_bits_before_prep'],
        'domain_symbolized_before_prep_sha256': proof['symbolized_before_prep_sha256'],
        'paired_proof_summary': str((args.pair_recheck/'summary.json').resolve()),
        'paired_proof_summary_sha256': digest(args.pair_recheck/'summary.json'),
        'paired_proof_implementation_sha256': recheck['proof']['implementation_sha256'],
        'paired_proof_undefined_semantics': recheck['proof']['undefined_value_model'],
        'domain_source_snapshot': str((args.domain_proof/'prove_domain_source.py').resolve()),
        'domain_source_snapshot_sha256': digest(args.domain_proof/'prove_domain_source.py'),
        'domain_projection_json_sha256': digest(args.domain_proof/'data_path.json'),
        'domain_summary': str((args.domain_proof/'summary.json').resolve()), 'domain_summary_sha256': digest(args.domain_proof/'summary.json'),
        'candidate_summary': str((args.candidate/'summary.json').resolve()), 'candidate_summary_sha256': digest(args.candidate/'summary.json'),
        'proof_log_sha256': {str(Path(path).resolve()): digest(Path(path)) for path in logs},
        'transfer_argument': 'The original response-to-decoder data projection proves the input domain with arbitrary control behavior. All decoder outputs equal on that domain, and all external consumers are among those outputs. Substitution therefore preserves outside state and outputs inductively from the shared reset under the same external inputs.',
        'physical_candidate_has_formal_monitors': False, 'certifier_sha256': digest(Path(__file__))}
    assert record['domain_source_snapshot_sha256'] == proof['source_sha256']
    args.output.write_text(json.dumps(record, indent=2)+'\n')
    print(json.dumps({'certificate': str(args.output), 'changed_cells': len(changed), 'decoder_outputs': len(record['decoder_outputs'])}))


if __name__ == '__main__':
    main()
