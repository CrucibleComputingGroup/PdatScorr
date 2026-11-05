#!/usr/bin/env python3
"""Compose decoder, original rd-domain, demux lowering, and RF output proofs."""
import argparse
import json
from pathlib import Path

from certify import checked_domain, checked_pair, digest
from lower_demux import expand_demuxes


def read(path):
    return json.loads(path.read_text())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--decoder-certificate', type=Path, required=True)
    parser.add_argument('--original-rf', type=Path, required=True)
    parser.add_argument('--prepared-rf', type=Path, required=True)
    parser.add_argument('--candidate', type=Path, required=True)
    parser.add_argument('--domain-proof', type=Path, required=True)
    parser.add_argument('--pair-recheck', type=Path, required=True)
    parser.add_argument('--lowering-proof', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert not args.output.exists()
    parent = read(args.decoder_certificate)
    assert parent['status'] == 'component_equivalence_and_domain_propagation_certified'
    assert parent['domain'] == 'program_alphabet'
    native_path, parent_path = Path(parent['native_original_json']), Path(parent['native_candidate_json'])
    assert digest(native_path) == parent['native_original_sha256']
    assert digest(parent_path) == parent['native_candidate_sha256']
    native, base = read(native_path), read(parent_path)
    original_rf = read(args.original_rf)['modules']['DecoderBase']
    native_module = native['modules']['datapath']
    for name, cell in original_rf['cells'].items():
        assert cell == native_module['cells'][name] == base['modules']['datapath']['cells'][name]
    for name, port in original_rf['ports'].items():
        assert port['bits'] == native_module['netnames']['u_backend.u_int_rf.'+name]['bits']
    manifest = read(args.prepared_rf/'manifest.json')
    expanded, changes = expand_demuxes(base, 'datapath', original_rf['cells'])
    assert expanded == read(args.prepared_rf/'whole_core.json')
    assert changes == manifest['unconditional_demux_lowering']
    assert digest(Path(__file__).with_name('lower_demux.py')) == manifest['lowering_source_sha256']
    expanded_rf = read(args.prepared_rf/'decoder.json')['modules']['DecoderBase']
    retained = set(original_rf['cells'])
    for change in changes:
        retained.remove(change['original_cell']); retained.update(change['generated_cells'])
    assert set(expanded_rf['cells']) == retained
    assert expanded_rf['ports'] == original_rf['ports']
    assert all(cell == expanded['modules']['datapath']['cells'][name] for name, cell in expanded_rf['cells'].items())
    component = read(args.candidate/'summary.json')
    assert component['prepared_manifest_sha256'] == digest(args.prepared_rf/'manifest.json')
    paired = checked_pair(args.pair_recheck, args.candidate)
    assert paired['component_kind'] == 'architectural_register_file'
    assert paired['proof']['property_counts']['assert'] == 2
    changed = read(args.candidate/'candidate_whole_core.json')
    a, b = expanded['modules']['datapath'], changed['modules']['datapath']
    assert a['ports'] == b['ports'] and a['netnames'] == b['netnames'] and set(a['cells']) == set(b['cells'])
    differences = {name for name in a['cells'] if a['cells'][name] != b['cells'][name]}
    assert differences == {item['cell'] for item in component['accepted']} and differences <= retained
    domain, protected = checked_domain(args.domain_proof)
    assert domain['literal_undefined_bits_after_sequential_lowering'] == 0
    assert digest(args.domain_proof/'lowered.json') == domain['lowered_json_sha256']
    lowered = read(args.domain_proof/'lowered.json')['modules']['DomainProof']
    assert not any(bit in ('x', 'z') for cell in lowered['cells'].values() for bits in cell['connections'].values() for bit in bits)
    assert domain['domain'] == 'program_alphabet' and domain['instruction_field_low'] == 7
    assert domain['projection']['target_net'] == 'u_backend.u_int_rf.comm_rd_idx_i'
    assert domain['projection']['target_width'] == 5
    assert domain['original_whole_core_sha256'] == parent['native_original_sha256']
    assert domain['output_field_values'] == manifest['rd_field_values']
    assert component['domain_expression'] == manifest['domains']['program_alphabet']['expression']
    assert digest(args.candidate/'harness.sv') == manifest['domains']['program_alphabet']['harness_sha256']
    projected = read(args.domain_proof/'data_path.json')['modules']['InstructionDataPath']
    assert projected['ports']['decoder_word']['bits'] == original_rf['ports']['comm_rd_idx_i']['bits']
    assert projected['ports']['instruction_i']['bits'] == native_module['ports']['instr_rdata_i']['bits']
    assert projected['ports']['response_valid']['bits'] == native_module['ports']['instr_rvalid_i']['bits']
    assert all(native_module['cells'][name] == b['cells'][name] for name in protected)
    # Check every original RF-driven bit consumed outside the RF, not just names.
    drivers = {bit for cell in original_rf['cells'].values() for port, direction in cell['port_directions'].items()
               if direction == 'output' for bit in cell['connections'][port] if isinstance(bit, int)}
    observed = {bit for port in original_rf['ports'].values() if port['direction'] == 'output' for bit in port['bits']}
    leaks = [(name, pin, bit) for name, cell in native_module['cells'].items() if name not in original_rf['cells']
             for pin, direction in cell['port_directions'].items() if direction == 'input'
             for bit in set(cell['connections'][pin]) & drivers - observed]
    leaks += [(name, 'top_output', bit) for name, port in native_module['ports'].items() if port['direction'] == 'output'
              for bit in set(port['bits']) & drivers - observed]
    assert not leaks
    lower = read(args.lowering_proof/'summary.json'); lp = lower['proof']
    assert lower['status'] == 'proved' and lp['proven'] and lp['property_counts']['assume'] == 0
    assert lower['original_rf_sha256'] == digest(args.original_rf)
    assert lower['lowering_source_sha256'] == manifest['lowering_source_sha256']
    assert lp['undefined_value_model'].startswith('Independent symbolic choices before process optimization')
    assert lp['implementation_sha256'] == digest(args.lowering_proof/'temporal_source.py')
    assert digest(args.lowering_proof/'proof/miter.aig') == lp['aig_sha256']
    assert lp['pdr']['returncode'] == 0 and not lp['pdr']['timeout']
    logs = [domain[key]['log'] for key in ('base', 'induction')] + [paired['proof']['pdr']['log'], lp['pdr']['log']]
    for proof_record in (domain['base'], domain['induction'], paired['proof']['pdr'], lp['pdr']):
        assert digest(Path(proof_record['log'])) == proof_record['log_sha256']
    assert not any(cell['type'] in ('$assume', '$assert', '$check', '$cover', '$anyseq', '$anyconst') for cell in b['cells'].values())
    record = {
        'status': 'decoder_and_register_specialization_composition_certified',
        'scope': 'Conditional whole-core external-output and outside-component state equivalence; no timing or capacity premise',
        'external_premises': parent['external_premises'], 'domain': 'program_alphabet',
        'domain_expression': parent['domain_expression'], 'timing_or_occupancy_premises': [],
        'native_original_json': str(native_path), 'native_original_sha256': digest(native_path),
        'native_candidate_json': str((args.candidate/'candidate_whole_core.json').resolve()),
        'native_candidate_sha256': digest(args.candidate/'candidate_whole_core.json'),
        'decoder_certificate': str(args.decoder_certificate.resolve()), 'decoder_certificate_sha256': digest(args.decoder_certificate),
        'register_read_outputs': ['issue_rs1_value_o', 'issue_rs2_value_o'], 'observed_register_read_bits': len(observed),
        'unobserved_external_register_consumers': leaks, 'original_rf_cells': len(original_rf['cells']),
        'unconditional_demux_lowering': changes, 'architectural_destination_field_values': domain['output_field_values'],
        'proved_constant_register_decodes': sorted(differences), 'capacity_parameters': component['capacity_parameters'],
        'native_ports_and_netnames_preserved': True, 'physical_candidate_has_formal_monitors': False,
        'domain_projection_cells_unchanged_by_all_specializations': True,
        'domain_projection_retained_control_cells': sorted(set(domain['projection']['retained_spill_write_control_cells'])),
        'domain_projection_retained_data_cells': sorted(set(domain['projection']['original_cell_slices'])),
        'domain_source_snapshot_sha256': domain['source_sha256'],
        'domain_symbolized_before_prep_sha256': domain['symbolized_before_prep_sha256'],
        'domain_symbolic_undefined_bits_before_prep': domain['symbolic_undefined_bits_before_prep'],
        'domain_literal_undefined_bits_after_sequential_lowering': 0,
        'domain_lowered_json_sha256': domain['lowered_json_sha256'],
        'safe_pair_implementation_sha256': paired['proof']['implementation_sha256'],
        'current_domain_supersedes_preparation_time_domain_proof': True,
        'evidence_summary_sha256': {str(path.resolve()): digest(path) for path in [args.domain_proof/'summary.json', args.pair_recheck/'summary.json', args.lowering_proof/'summary.json', args.candidate/'summary.json']},
        'proof_log_sha256': {str(Path(path).resolve()): digest(Path(path)) for path in logs},
        'transfer_argument': 'Certified decoder substitution preserves outside state. The original rd-field data projection is unchanged by both substitutions. Its proved input range and unconditional full-arm demux equivalence enable the RF two-read-port equivalence proof. These two ports cover every external RF consumer; all remaining native logic is unchanged, so substitution preserves external outputs and all outside state under the same inputs and initial reset.',
        'certifier_sha256': digest(Path(__file__))}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2)+'\n')
    print(json.dumps({'certificate': str(args.output), 'register_constant_decodes': len(differences)}))


if __name__ == '__main__':
    main()
