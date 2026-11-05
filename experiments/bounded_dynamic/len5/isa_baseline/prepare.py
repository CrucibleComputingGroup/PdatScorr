#!/usr/bin/env python3
"""Extract the original combinational decoder and explicit instruction domains.

All decoder outputs are observed. Original cell/bit identities are retained for
later integration into the fixed whole core. This prepares an experiment only.
"""
from __future__ import annotations
import argparse
import copy
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
sys.path.insert(0, str(REPO))
sys.path.insert(0, str(HERE.parent))
from odc.temporal import checked_yosys, digest, export_design, yosys_path
from odc.state_candidates import scalar_constant_candidates
from prepare_frontend import PRE_FPU_PIN, workspace_root

PREFIX = 'u_backend.u_issue_stage.u_issue_decoder.'
OUTPUTS = ('issue_type_o', 'except_code_o', 'assigned_eu_o', 'skip_eu_o', 'eu_ctl_o',
           'mem_crit_o', 'order_crit_o', 'rs1_req_o', 'rs1_is_pc_o', 'rs2_req_o',
           'rs2_is_imm_o', 'rd_upd_o', 'imm_format_o')


def extract_decoder(whole):
    module = whole['modules']['datapath']
    instruction = module['netnames'][PREFIX+'instruction_i']['bits']
    ports = {'instruction_i': {'direction': 'input', 'bits': instruction}}
    ports.update({name: {'direction': 'output', 'bits': module['netnames'][PREFIX+name]['bits']}
                  for name in OUTPUTS})
    driver = {}
    for name, cell in module['cells'].items():
        for port, direction in cell['port_directions'].items():
            if direction == 'output':
                for bit in cell['connections'][port]:
                    if isinstance(bit, int):
                        assert bit not in driver, ('Multiple drivers', bit)
                        driver[bit] = name
    retained, visiting = set(), set()
    def visit(bit):
        if not isinstance(bit, int) or bit in instruction:
            return
        assert bit in driver, ('Undeclared cone input', bit)
        name = driver[bit]
        if name in retained:
            return
        assert name not in visiting, 'Combinational loop'
        cell = module['cells'][name]
        assert not any(token in cell['type'].lower() for token in ('ff', 'latch', 'mem', 'any', 'assume', 'assert'))
        assert cell['type'].startswith('$')
        visiting.add(name)
        for port, direction in cell['port_directions'].items():
            if direction == 'input':
                for other in cell['connections'][port]:
                    visit(other)
        visiting.remove(name)
        retained.add(name)
    for port in ports.values():
        for bit in port['bits']:
            visit(bit)
    all_bits = set(instruction)
    for name in retained:
        for bits in module['cells'][name]['connections'].values():
            all_bits.update(bits)
    nets = {name: copy.deepcopy(net) for name, net in module['netnames'].items()
            if set(net['bits']) <= all_bits and name.startswith(PREFIX)}
    for name, port in ports.items():
        nets[name] = {'hide_name': 0, 'attributes': {}, 'bits': port['bits']}
    return {'modules': {'DecoderBase': {'attributes': {'top': '1'}, 'ports': ports,
            'netnames': nets, 'cells': {name: copy.deepcopy(module['cells'][name]) for name in sorted(retained)}}}}


def domain_expressions(disassembly, instruction_package):
    words = sorted({int(word, 16) for addr, word in re.findall(
        r'(?m)^\s*([0-9a-f]+):\s+([0-9a-f]{8})\s', disassembly) if int(addr, 16) < 0x38})
    assert len(words) == 14
    patterns = []
    for name, bits in re.findall(r'localparam logic \[31:0\] (\w+) = 32\x27b([01?]{32});', instruction_package):
        mask = int(''.join('0' if b == '?' else '1' for b in bits), 2)
        value = int(bits.replace('?', '0'), 2)
        if any(word & mask == value for word in words):
            patterns.append({'instruction': name, 'mask': mask, 'value': value})
    assert {x['instruction'] for x in patterns} == {'LUI', 'ADDI', 'ADDIW', 'LD', 'SD', 'BNE', 'SB', 'JAL'}
    isa = ' || '.join(f'((instruction_i & 32\'h{x["mask"]:08x}) == 32\'h{x["value"]:08x})' for x in patterns)
    alphabet = ' || '.join(f'(instruction_i == 32\'h{word:08x})' for word in words)
    return words, patterns, {'isa_operations': f'(instruction_i == 0) || {isa}',
                             'program_alphabet': f'(instruction_i == 0) || {alphabet}'}


def harness(module, expression):
    lines = ['module TemporalMiter(input [31:0] instruction_i);']
    associations = {'a': [], 'b': []}
    for name, port in module['ports'].items():
        for label in associations:
            if port['direction'] == 'input':
                associations[label].append(f'.{name}({name})')
            else:
                lines.append(f'wire [{len(port["bits"])-1}:0] {label}_{name};')
                associations[label].append(f'.{name}({label}_{name})')
    lines += [f'DecoderBase reference({", ".join(associations["a"])});',
              f'DecoderCandidate candidate({", ".join(associations["b"])});',
              'always @* begin', f'  assume({expression});']
    lines += [f'  assert(a_{name} == b_{name});' for name in OUTPUTS]
    return '\n'.join(lines + ['end', 'endmodule', ''])


def main():
    workspace = workspace_root(HERE)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--frontend', type=Path, default=workspace/'experiments/bounded_dynamic/len5/build/pre_fpu_frontend')
    parser.add_argument('--disassembly', type=Path, default=HERE.parent/'results/streaming_fetchgap2_v2/program.disasm')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--yosys', default=str(workspace/'tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys'))
    args = parser.parse_args()
    frontend, out = args.frontend.resolve(), args.output.resolve()
    manifest = json.loads((frontend/'manifest.json').read_text())
    assert manifest['upstream_commit'] == PRE_FPU_PIN and manifest['original_sha256'] == manifest['prepared_sha256']
    assert digest(frontend/'normalized.il') == manifest['normalized_il_sha256']
    out.mkdir(parents=True, exist_ok=False)
    execution = checked_yosys(args.yosys, f'read_rtlil {yosys_path(frontend/"normalized.il")}\n'
        f'check -assert\nwrite_json {yosys_path(out/"whole_core.json")}\n', out, 'prepare_whole', 60)
    whole = json.loads((out/'whole_core.json').read_text())
    decoder = extract_decoder(whole)
    (out/'decoder.json').write_text(json.dumps(decoder)+'\n')
    export_design(decoder, 'DecoderBase', 'DecoderBase', out/'decoder.v', args.yosys, 60)
    words, patterns, domains = domain_expressions(args.disassembly.read_text(),
        (frontend/'source/rtl/packages/instr_pkg.sv').read_text())
    for name, expression in domains.items():
        (out/(name+'.sv')).write_text(harness(decoder['modules']['DecoderBase'], expression))
    candidates = scalar_constant_candidates(decoder, 'DecoderBase')
    record = {'scope': 'Prepared combinational decoder baseline; no hardware saving or full-core equivalence claim',
        'frontend_manifest_sha256': digest(frontend/'manifest.json'), 'upstream_commit': PRE_FPU_PIN,
        'original_normalized_il_sha256': digest(frontend/'normalized.il'),
        'whole_core_json_sha256': digest(out/'whole_core.json'), 'decoder_json_sha256': digest(out/'decoder.json'),
        'script_sha256': digest(Path(__file__)), 'source_disassembly_sha256': digest(args.disassembly),
        'capacity_parameters': manifest['capacity_parameters_unchanged'], 'execution': execution,
        'observed_decoder_outputs': {name: len(decoder['modules']['DecoderBase']['ports'][name]['bits']) for name in OUTPUTS},
        'decoder_cells': len(decoder['modules']['DecoderBase']['cells']), 'scalar_candidate_attempts': len(candidates),
        'isa_operations': patterns, 'program_alphabet': [f'{word:08x}' for word in words],
        'bubble_word_in_both_domains': '00000000',
        'privilege_context': 'Original whole-core priv_mode_i already constant machine mode; no new assumption',
        'domains': {name: {'expression': expression, 'harness_sha256': digest(out/(name+'.sv'))} for name, expression in domains.items()}}
    (out/'manifest.json').write_text(json.dumps(record, indent=2)+'\n')
    print(json.dumps({'decoder_cells': record['decoder_cells'], 'scalar_candidate_attempts': len(candidates)}))


if __name__ == '__main__':
    main()
