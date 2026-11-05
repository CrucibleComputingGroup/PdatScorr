#!/usr/bin/env python3
"""Prove response-word domains reach the actual decoder through native storage.

Project only instruction-bearing data bits from original cells. Mux selectors
and write enables become arbitrary inputs, broadening allowed control behavior.
Native clock/reset, all instruction state, data transitions, and muxes remain.
Per-word domain helpers are assertions, never internal assumptions.
"""
from __future__ import annotations
import argparse
import copy
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[3]))
sys.path.insert(0, str(HERE.parent))
from odc.temporal import checked_yosys, digest, export_design, formal_lower_command, parameter_int, proof_passed, run_command, validate_single_clock, yosys_path
from prepare_frontend import workspace_root
from prepare import PREFIX


def data_projection(whole, target_name=PREFIX+'instruction_i', target_width=32):
    source = whole['modules']['datapath']
    instruction = source['ports']['instr_rdata_i']['bits']
    target = source['netnames'][target_name]['bits']
    assert len(target) == target_width
    clock = source['ports']['clk_i']['bits']; reset = source['ports']['rst_ni']['bits']
    drivers = {}
    for name, cell in source['cells'].items():
        for port, direction in cell['port_directions'].items():
            if direction == 'output':
                for index, bit in enumerate(cell['connections'][port]):
                    if isinstance(bit, int):
                        assert bit not in drivers
                        drivers[bit] = (name, port, index)
    selected, controls, pending, visited = {}, set(), list(target), set()
    while pending:
        bit = pending.pop()
        if not isinstance(bit, int) or bit in instruction or bit in visited:
            continue
        visited.add(bit)
        name, port, index = drivers[bit]
        cell = source['cells'][name]; kind = cell['type']; con = cell['connections']
        selected.setdefault(name, set()).add(index)
        if kind in ('$adff', '$adffe', '$aldff'):
            reset_pin = 'ALOAD' if kind == '$aldff' else 'ARST'
            assert port == 'Q' and con['CLK'] == clock and con[reset_pin] == reset
            assert parameter_int(cell['parameters']['CLK_POLARITY']) == 1
            assert parameter_int(cell['parameters'][reset_pin+'_POLARITY']) == 0
            if kind == '$aldff':
                assert con['AD'][index] == '0', 'Only native constant-zero asynchronous loads supported'
            pending.append(con['D'][index])
            controls.update(con.get('EN', []))
        elif kind == '$mux':
            assert port == 'Y'
            pending += [con['A'][index], con['B'][index]]
            controls.update(con['S'])
        elif kind == '$bmux':
            assert port == 'Y'
            width = len(con['Y'])
            pending += con['A'][index::width]
            controls.update(con['S'])
        elif kind == '$bwmux':
            assert port == 'Y'
            pending += [con['A'][index], con['B'][index]]
            controls.add(con['S'][index])
        else:
            raise ValueError('Unsupported instruction data-path cell: '+kind)
    cells, state_words = {}, []
    for name, indices_set in selected.items():
        indices = sorted(indices_set)
        original = source['cells'][name]; cell = copy.deepcopy(original)
        con = cell['connections']; kind = cell['type']
        if kind in ('$adff', '$adffe', '$aldff'):
            for port in ('D', 'Q'):
                con[port] = [con[port][i] for i in indices]
            if kind == '$aldff':
                con['AD'] = [con['AD'][i] for i in indices]
                assert set(con['AD']) == {'0'}
            else:
                bits = cell['parameters']['ARST_VALUE'][::-1]
                assert all(bits[i] == '0' for i in indices)
                cell['parameters']['ARST_VALUE'] = ''.join(bits[i] for i in indices)[::-1]
            state_words.append({'cell': name, 'bits': con['Q'], 'original_indices': indices})
        elif kind in ('$mux', '$bwmux'):
            for port in ('A', 'B', 'Y'):
                con[port] = [con[port][i] for i in indices]
            if kind == '$bwmux':
                con['S'] = [con['S'][i] for i in indices]
        elif kind == '$bmux':
            width = len(con['Y'])
            con['A'] = [con['A'][base+i] for base in range(0, len(con['A']), width) for i in indices]
            con['Y'] = [con['Y'][i] for i in indices]
        cell['parameters']['WIDTH'] = format(len(indices), '032b')
        cells[name] = cell
    assert all(len(word['bits']) == target_width for word in state_words), 'Expected complete native fields'
    driven = {b for cell in cells.values() for port, direction in cell['port_directions'].items()
              if direction == 'output' for b in cell['connections'][port]}
    # Keep actual spill-write gating so invalid response payload is unrestricted.
    # Upstream selectors derive from a shared control-state vector; retain their
    # combinational relations while allowing that vector to vary arbitrarily.
    response_valid = source['ports']['instr_rvalid_i']['bits']
    primary_inputs = {b for p in source['ports'].values() if p['direction'] == 'input' for b in p['bits']}
    control_cells, control_leaves, active = set(), set(), set()
    def keep_control(bit):
        if not isinstance(bit, int) or bit in driven:
            return
        if bit in primary_inputs:
            control_leaves.add(bit); return
        name, port, index = drivers[bit]
        original = source['cells'][name]
        if 'ff' in original['type'].lower():
            control_leaves.add(bit); return
        assert not any(token in original['type'].lower() for token in ('latch', 'mem', 'any', 'assume', 'assert'))
        if name in control_cells:
            return
        assert name not in active
        active.add(name)
        for pin, direction in original['port_directions'].items():
            if direction == 'input':
                for other in original['connections'][pin]:
                    keep_control(other)
        active.remove(name)
        assert name not in cells
        cells[name] = copy.deepcopy(original)
        control_cells.add(name)
    spill_prefix = 'u_fetch_stage.u_mem_if.u_ans_reg.gen_spill_cell_gen.'
    for signal in ('a_en', 'b_en'):
        for bit in source['netnames'][spill_prefix+signal]['bits']:
            assert bit in controls
            keep_control(bit)
    # Bitwise write masks must retain their native whole-field correlations.
    # Independent mask bits could manufacture an impossible torn instruction
    # field, so preserve their combinational decode from arbitrary control Q.
    bitmask_roots = [bit for cell in list(cells.values()) if cell['type'] == '$bwmux'
                     for bit in cell['connections']['S']]
    for bit in bitmask_roots:
        keep_control(bit)
    # Native array bounds and update selectors jointly suppress X defaults.
    # Preserve every selector's combinational relation; only unrelated FF-Q
    # leaves remain arbitrary, so no internal reachability fact is assumed.
    for bit in list(controls):
        keep_control(bit)
    driven = {b for cell in cells.values() for port, direction in cell['port_directions'].items()
              if direction == 'output' for b in cell['connections'][port]}
    controls.update(control_leaves)
    # Controls already driven by retained data state keep that relation.
    arbitrary = sorted(b for b in controls if isinstance(b, int) and b not in driven
                       and b not in instruction + clock + reset + response_valid)
    ports = {'clk_i': {'direction': 'input', 'bits': clock}, 'rst_ni': {'direction': 'input', 'bits': reset},
             'instruction_i': {'direction': 'input', 'bits': instruction},
             'response_valid': {'direction': 'input', 'bits': response_valid},
             'decoder_word': {'direction': 'output', 'bits': target}}
    ports.update({f'control_{i}': {'direction': 'input', 'bits': [bit]} for i, bit in enumerate(arbitrary)})
    ports.update({f'state_word_{i}': {'direction': 'output', 'bits': word['bits']} for i, word in enumerate(state_words)})
    nets = {name: {'hide_name': 0, 'attributes': {}, 'bits': port['bits']} for name, port in ports.items()}
    result = {'modules': {'InstructionDataPath': {'attributes': {'top': '1'}, 'ports': ports, 'netnames': nets, 'cells': cells}}}
    audit = {'original_cell_slices': {name: sorted(indices) for name, indices in selected.items()},
             'target_net': target_name, 'target_width': target_width,
             'state_words': state_words, 'arbitrary_control_bits': arbitrary,
             'retained_spill_write_control_cells': sorted(control_cells), 'internal_assumptions_added': 0,
             'method': 'Exact native data-cell bit projection with arbitrary mux/enable controls; control overapproximation only'}
    return result, audit


def main():
    workspace = workspace_root(HERE)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepared', type=Path, required=True)
    parser.add_argument('--domain', choices=('isa_operations', 'program_alphabet'), required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--target-net', default=PREFIX+'instruction_i')
    parser.add_argument('--target-width', type=int, default=32)
    parser.add_argument('--instruction-field-low', type=int, default=0)
    parser.add_argument('--yosys', default=str(workspace/'tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys'))
    args = parser.parse_args()
    prepared, out = args.prepared.resolve(), args.output.resolve(); out.mkdir(parents=True, exist_ok=False)
    meta = json.loads((prepared/'manifest.json').read_text())
    assert digest(prepared/'whole_core.json') == meta['whole_core_json_sha256']
    original = json.loads((prepared/'whole_core.json').read_text())
    (out/'prove_domain_source.py').write_bytes(Path(__file__).read_bytes())
    model, audit = data_projection(original, args.target_net, args.target_width)
    export_design(model, 'InstructionDataPath', 'InstructionDataPath', out/'data_path.v', args.yosys, 30)
    ports = model['modules']['InstructionDataPath']['ports']
    inputs = [f'input [{len(p["bits"])-1}:0] {n}' for n, p in ports.items() if p['direction'] == 'input']
    outputs = [n for n, p in ports.items() if p['direction'] == 'output']
    domain = meta['domains'][args.domain]['expression']
    lines = ['module DomainProof('+', '.join(inputs)+');']
    lines += [f'wire [{args.target_width-1}:0] {name};' for name in outputs]
    lines += ['InstructionDataPath dut('+', '.join(f'.{name}({name})' for name in ports)+');',
              'always @* begin', '  if ($initstate) assume(!rst_ni);', '  if (rst_ni && response_valid) assume('+domain+');']
    output_values = None
    if args.target_width == 32:
        assert args.instruction_field_low == 0
        output_domain = domain
    else:
        assert args.domain == 'program_alphabet' and 0 <= args.instruction_field_low <= 32-args.target_width
        output_values = sorted({0, *((int(word, 16) >> args.instruction_field_low) & ((1 << args.target_width)-1)
                                      for word in meta['program_alphabet'])})
        output_domain = ' || '.join(f'(instruction_i == {args.target_width}\'d{value})' for value in output_values)
    lines += ['  assert('+output_domain.replace('instruction_i', name)+');' for name in outputs]
    lines += ['end', 'endmodule', '']
    (out/'harness.sv').write_text('\n'.join(lines))
    record = {'status': 'running', 'scope': 'Original decoder-domain propagation under external ISA/alphabet response-word premise only; no timing constraint',
              'external_word_premise_guard': 'rst_ni && instr_rvalid_i',
              'projection': audit, 'domain': args.domain, 'original_whole_core_sha256': digest(prepared/'whole_core.json'),
              'output_field_values': output_values, 'instruction_field_low': args.instruction_field_low,
              'source_sha256': digest(Path(__file__)), 'harness_sha256': digest(out/'harness.sv')}
    try:
        smt = out/'model.smt2'
        checked_yosys(args.yosys, f'read_json {yosys_path(out/"data_path.json")}\n'
            'bwmuxmap\nbmuxmap\nsetundef -anyseq\n'
            f'write_json {yosys_path(out/"symbolized_before_prep.json")}\n'
            f'read_verilog -formal -sv {yosys_path(out/"harness.sv")}\n'
            'prep -top DomainProof -flatten\n'+formal_lower_command(args.yosys)+'check -assert\nopt_dff\nasync2sync\ndffunmap\n'
            f'write_json {yosys_path(out/"lowered.json")}\nwrite_smt2 -wires {yosys_path(smt)}\n', out, 'export', 30)
        record['clock_model'] = validate_single_clock(json.loads((out/'lowered.json').read_text()), 'DomainProof')
        record['undefined_semantics'] = 'Native JSON primitive mapping then setundef-anyseq BEFORE prep/opt; no Verilog roundtrip for projected data'
        symbolic = json.loads((out/'symbolized_before_prep.json').read_text())['modules']['InstructionDataPath']
        record['symbolic_undefined_bits_before_prep'] = sum(len(c['connections']['Y']) for c in symbolic['cells'].values() if c['type'] == '$anyseq')
        assert not any(bit in ('x', 'z') for cell in symbolic['cells'].values() for bits in cell['connections'].values() for bit in bits)
        record['symbolized_before_prep_sha256'] = digest(out/'symbolized_before_prep.json')
        command = [str(Path(args.yosys).with_name('yosys-smtbmc')), '-s', 'z3', '-t', '3', '--noprogress']
        record['base'] = run_command(command+[str(smt)], out/'base.log', 30)
        record['induction'] = run_command(command+['-i', str(smt)], out/'induction.log', 30)
        record['status'] = 'proved' if proof_passed(record['base']) and proof_passed(record['induction']) else 'unproved'
    except (AssertionError, RuntimeError, ValueError, OSError, KeyError) as error:
        record.update(status='failed', error=str(error))
    (out/'summary.json').write_text(json.dumps(record, indent=2)+'\n')
    print(json.dumps({'status': record['status'], 'instruction_state_words': len(audit['state_words']),
                      'arbitrary_control_bits': len(audit['arbitrary_control_bits'])}))
    return 0 if record['status'] == 'proved' else 1


if __name__ == '__main__':
    raise SystemExit(main())
