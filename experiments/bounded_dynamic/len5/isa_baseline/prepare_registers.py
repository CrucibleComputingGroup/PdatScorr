#!/usr/bin/env python3
"""Prepare automatic architectural-RF pruning after a proved rd-field domain.

The original RF capacities, storage, reads, and writes remain in this component.
Only a subsequent exhaustive scalar search may suggest constant write decodes.
"""
import argparse
import copy
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[3]))
from odc.temporal import digest
from odc.state_candidates import scalar_constant_candidates
from lower_demux import expand_demuxes
from certify import checked_domain


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepared', type=Path, required=True)
    parser.add_argument('--base-candidate', type=Path, required=True)
    parser.add_argument('--domain-proof', type=Path, required=True)
    parser.add_argument('--decoder-certificate', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve(); out.mkdir(parents=True, exist_ok=False)
    (out/'prepare_registers_source.py').write_bytes(Path(__file__).read_bytes())
    original = json.loads((args.prepared/'whole_core.json').read_text())
    base = json.loads((args.base_candidate/'candidate_whole_core.json').read_text())
    baseline = json.loads((args.base_candidate/'summary.json').read_text())
    assert baseline['status'] == 'decoder_equivalence_proved_native_candidate_emitted'
    certificate = json.loads(args.decoder_certificate.read_text())
    assert certificate['status'] == 'component_equivalence_and_domain_propagation_certified'
    assert certificate['native_candidate_sha256'] == digest(args.base_candidate/'candidate_whole_core.json')
    proof, protected = checked_domain(args.domain_proof)
    assert proof['projection']['target_net'] == 'u_backend.u_int_rf.comm_rd_idx_i'
    assert proof['instruction_field_low'] == 7 and proof['projection']['target_width'] == 5
    assert proof['original_whole_core_sha256'] == digest(args.prepared/'whole_core.json')
    for name in protected:
        assert base['modules']['datapath']['cells'][name] == original['modules']['datapath']['cells'][name], name
    module = base['modules']['datapath']
    prefix = 'u_backend.u_int_rf.'
    inputs = ('clk_i', 'rst_ni', 'comm_valid_i', 'comm_rd_idx_i', 'comm_rd_value_i', 'issue_rs1_idx_i', 'issue_rs2_idx_i')
    outputs = ('issue_rs1_value_o', 'issue_rs2_value_o')
    ports = {name: {'direction': 'input' if name in inputs else 'output',
                    'bits': module['netnames'][prefix+name]['bits']} for name in [*inputs, *outputs]}
    input_bits = {bit for name in inputs for bit in ports[name]['bits']}
    driver = {}
    for name, cell in module['cells'].items():
        for port, direction in cell['port_directions'].items():
            if direction == 'output':
                for bit in cell['connections'][port]:
                    if isinstance(bit, int):
                        assert bit not in driver
                        driver[bit] = name
    retained = set()
    def visit(bit):
        if not isinstance(bit, int) or bit in input_bits:
            return
        name = driver[bit]
        if name in retained:
            return
        retained.add(name)
        for port, direction in module['cells'][name]['port_directions'].items():
            if direction == 'input':
                for item in module['cells'][name]['connections'][port]:
                    visit(item)
    for name in outputs:
        for bit in ports[name]['bits']:
            visit(bit)
    original_rf = {'modules': {'DecoderBase': {'attributes': {'top': '1'}, 'ports': copy.deepcopy(ports),
        'netnames': {name: copy.deepcopy(net) for name, net in module['netnames'].items() if name.startswith(prefix)},
        'cells': {name: copy.deepcopy(module['cells'][name]) for name in retained}}}}
    (out/'original_rf.json').write_text(json.dumps(original_rf)+'\n')
    base, lowering = expand_demuxes(base, 'datapath', retained)
    for change in lowering:
        retained.remove(change['original_cell'])
        retained.update(change['generated_cells'])
    module = base['modules']['datapath']
    nets = {name: copy.deepcopy(net) for name, net in module['netnames'].items() if name.startswith(prefix)}
    for name, port in ports.items():
        nets[name] = {'hide_name': 0, 'attributes': {}, 'bits': port['bits']}
    rf = {'modules': {'DecoderBase': {'attributes': {'top': '1'}, 'ports': ports, 'netnames': nets,
                                     'cells': {name: copy.deepcopy(module['cells'][name]) for name in retained}}}}
    (out/'whole_core.json').write_text(json.dumps(base)+'\n')
    (out/'decoder.json').write_text(json.dumps(rf)+'\n')
    values = proof['output_field_values']
    expression = ' || '.join(f'(comm_rd_idx_i == 5\'d{value})' for value in values)
    declarations = [f'input [{len(ports[name]["bits"])-1}:0] {name}' for name in inputs]
    lines = ['module TemporalMiter('+', '.join(declarations)+');']
    for side in ('a', 'b'):
        for name in outputs:
            lines.append(f'wire [{len(ports[name]["bits"])-1}:0] {side}_{name};')
        connections = [f'.{name}({name})' for name in inputs] + [f'.{name}({side}_{name})' for name in outputs]
        lines.append(('DecoderBase reference' if side == 'a' else 'DecoderCandidate candidate')+'('+', '.join(connections)+');')
    lines += ['always @* begin', '  if ($initstate) assume(!rst_ni);', '  assume('+expression+');']
    lines += [f'  assert(a_{name} == b_{name});' for name in outputs]
    lines += ['end', 'endmodule', '']
    (out/'program_alphabet.sv').write_text('\n'.join(lines))
    meta = {'component_kind': 'architectural_register_file', 'component_has_state': True,
        'scope': 'Program-alphabet architectural destination-register restriction, no timing information or capacity edits',
        'decoder_json_sha256': digest(out/'decoder.json'), 'whole_core_json_sha256': digest(out/'whole_core.json'),
        'capacity_parameters': baseline['capacity_parameters'], 'rd_field_values': values,
        'parent_candidate_summary_sha256': digest(args.base_candidate/'summary.json'),
        'domain_propagation_summary_sha256': digest(args.domain_proof/'summary.json'),
        'decoder_certificate_sha256': digest(args.decoder_certificate),
        'propagation_data_cells_unchanged_by_decoder_specialization': True,
        'domains': {'program_alphabet': {'expression': expression, 'harness_sha256': digest(out/'program_alphabet.sv')}},
        'script_sha256': digest(Path(__file__)), 'component_cells': len(retained),
        'unconditional_demux_lowering': lowering, 'lowering_source_sha256': digest(HERE/'lower_demux.py'),
        'scalar_candidate_attempts': len(scalar_constant_candidates(rf, 'DecoderBase'))}
    (out/'manifest.json').write_text(json.dumps(meta, indent=2)+'\n')
    print(json.dumps({'component_cells': len(retained), 'scalar_candidate_attempts': meta['scalar_candidate_attempts'], 'rd_values': values}))


if __name__ == '__main__':
    main()
