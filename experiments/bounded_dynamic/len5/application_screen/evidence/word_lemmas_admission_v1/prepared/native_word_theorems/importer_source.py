"""Import proved instruction-domain theorems into a native admission query.

The only added assumptions are the seven conclusions of a previously proved
native data-path projection. Certificate replay, exact native slices, and a
fresh export of the small projection bind those conclusions to this design.
This helper neither proves an admission bound nor authorizes a hardware rewrite.
"""
from __future__ import annotations
import copy
import json
import os
from pathlib import Path
import sys

from odc.temporal import checked_yosys, digest, parameter_int, proof_passed, yosys_path
from certified_decoder import import_decoder, validate_contract

TARGET = 'u_backend.u_issue_stage.u_issue_decoder.instruction_i'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read(path):
    return json.loads(Path(path).read_text())


def check_unbounded_domain_proof(summary, domain):
    require(summary['status'] == 'proved' and proof_passed(summary['base']) and proof_passed(summary['induction']),
            'Both reset base and induction must be proved')
    base, induction = summary['base'], summary['induction']
    require('-i' not in base['argv'] and '-i' in induction['argv'], 'Bounded checks cannot substitute for induction')
    for result in (base, induction):
        require(result['argv'][-1] == str(domain/'model.smt2'), 'Solver checked a different theorem model')
        require(digest(Path(result['log'])) == result['log_sha256'], 'Theorem solver log changed')
    require('Temporal induction successful.' in Path(induction['log']).read_text(), 'Missing unbounded induction result')


def native_lemma_bindings(original, design, projected, audit):
    """Independently rebuild every projected primitive and bind its FF-Q bits."""
    a, b = original['modules']['datapath'], design['modules']['datapath']
    p = projected['modules']['InstructionDataPath']
    require(audit['target_net'] == TARGET and audit['target_width'] == 32,
            'Only the certified full instruction-word projection is supported')
    require(audit['internal_assumptions_added'] == 0, 'Projection contains internal premises')
    data = audit['original_cell_slices']; controls = audit['retained_spill_write_control_cells']
    require(set(p['cells']) == set(data) | set(controls), 'Projection cell inventory changed')
    require(not set(data) & set(controls), 'Projection data/control inventories overlap')
    for name, indices in data.items():
        require(indices == sorted(set(indices)), 'Native slice indices are not unique and ordered')
        cell = copy.deepcopy(a['cells'][name]); con = cell['connections']; kind = cell['type']
        require(cell == b['cells'][name], 'Imported design changed a projected native data cell')
        if kind in ('$adff', '$adffe', '$aldff'):
            for pin in ('D', 'Q'): con[pin] = [con[pin][i] for i in indices]
            if kind == '$aldff': con['AD'] = [con['AD'][i] for i in indices]
            else: cell['parameters']['ARST_VALUE'] = ''.join(cell['parameters']['ARST_VALUE'][::-1][i] for i in indices)[::-1]
        elif kind in ('$mux', '$bwmux'):
            for pin in ['A', 'B', 'Y'] + (['S'] if kind == '$bwmux' else []):
                con[pin] = [con[pin][i] for i in indices]
        elif kind == '$bmux':
            width = len(con['Y'])
            con['A'] = [con['A'][j+i] for j in range(0, len(con['A']), width) for i in indices]
            con['Y'] = [con['Y'][i] for i in indices]
        else: raise ValueError('Unsupported projected primitive: '+kind)
        cell['parameters']['WIDTH'] = format(len(indices), '032b')
        require(cell == p['cells'][name], 'Native primitive slice differs from proved projection')
    for name in controls:
        require(a['cells'][name] == b['cells'][name] == p['cells'][name], 'Native preserved control changed')
    for pin, native in [('clk_i', 'clk_i'), ('rst_ni', 'rst_ni'),
                        ('instruction_i', 'instr_rdata_i'), ('response_valid', 'instr_rvalid_i')]:
        require(p['ports'][pin]['bits'] == a['ports'][native]['bits'], 'Projection external binding changed')
    require(p['ports']['decoder_word']['bits'] == a['netnames'][TARGET]['bits'] == b['netnames'][TARGET]['bits'],
            'Decoder word aliases changed')
    words = audit['state_words']
    require(len(words) == 6 and len({w['cell'] for w in words}) == 6, 'Expected six unique native stored words')
    lemmas = []
    for i, word in enumerate(words):
        name, bits = word['cell'], word['bits']; cell = a['cells'][name]
        require(cell['type'] in ('$adff', '$adffe', '$aldff'), 'Lemma is not a native state word')
        require(word['original_indices'] == data[name], 'State-word slice differs from proved data slice')
        require(bits == [cell['connections']['Q'][j] for j in word['original_indices']], 'State-word Q binding changed')
        require(len(bits) == 32 and len(set(bits)) == 32 and all(type(bit) is int for bit in bits), 'Invalid state-word bits')
        require(p['ports'][f'state_word_{i}']['bits'] == bits, 'Proved state-word output binding changed')
        reset_pin = 'ALOAD' if cell['type'] == '$aldff' else 'ARST'
        require(cell['connections']['CLK'] == a['ports']['clk_i']['bits'] and
                cell['connections'][reset_pin] == a['ports']['rst_ni']['bits'] and
                parameter_int(cell['parameters']['CLK_POLARITY']) == 1 and
                parameter_int(cell['parameters'][reset_pin+'_POLARITY']) == 0,
                'Native state clock/reset domain changed')
        lemmas.append({'name': f'state_word_{i}', 'bits': list(bits), 'native_cell': name,
                       'original_indices': list(word['original_indices'])})
    lemmas.append({'name': 'decoder_word', 'bits': list(p['ports']['decoder_word']['bits']), 'native_net': TARGET})
    require({name for name, port in p['ports'].items() if port['direction'] == 'output'} ==
            {x['name'] for x in lemmas}, 'Projection has extra or missing theorem outputs')
    return lemmas


def replay_domain_export(domain, directory, yosys, timeout):
    """Reproduce the recorded small proof model; this runs no SMT/PDR query."""
    script = (domain/'export.ys').read_text()
    before = (f'read_json {yosys_path(domain/"data_path.json")}\n'
              'bwmuxmap\nbmuxmap\nsetundef -anyseq\n'
              f'write_json {yosys_path(domain/"symbolized_before_prep.json")}\n'
              f'read_verilog -formal -sv {yosys_path(domain/"harness.sv")}\n'
              'prep -top DomainProof -flatten\nchformal -lower\ncheck -assert\nopt_dff\nasync2sync\ndffunmap\n')
    after = (f'write_json {yosys_path(domain/"lowered.json")}\n'
             f'write_smt2 -wires {yosys_path(domain/"model.smt2")}\n')
    require(script in (before+after, before+'setundef -anyseq\n'+after), 'Unsupported or changed domain export pipeline')
    directory.mkdir()
    fresh = script
    for name in ('symbolized_before_prep.json', 'lowered.json', 'model.smt2'):
        fresh = fresh.replace(yosys_path(domain/name), yosys_path(directory/name))
    execution = checked_yosys(yosys, fresh, directory, 'regenerate', timeout)
    for name in ('symbolized_before_prep.json', 'lowered.json'):
        require(read(domain/name) == read(directory/name), 'Regenerated domain JSON differs: '+name)
    require(digest(domain/'model.smt2') == digest(directory/'model.smt2'), 'Regenerated SMT model differs')
    return execution


def _add_domain_assumptions(design, lemmas, allowed):
    """Mechanical theorem encoding; callers must establish proof applicability."""
    result = copy.deepcopy(design); m = result['modules']['datapath']
    all_bits = [bit for c in m['cells'].values() for bs in c['connections'].values() for bit in bs if type(bit) is int]
    all_bits += [bit for n in [*m['ports'].values(), *m['netnames'].values()] for bit in n['bits'] if type(bit) is int]
    next_bit = max(all_bits)+1
    new_cells = []
    for index, lemma in enumerate(lemmas):
        bits = lemma['bits']; width = len(bits); terms = []
        for j, word in enumerate(sorted(allowed)):
            require(type(word) is int and 0 <= word < 1 << width, 'Lemma alphabet value exceeds word width')
            name = f'$pscorr_domain_lemma_{index}_word_{j}'
            require(name not in m['cells'], 'Lemma cell-name collision')
            out = next_bit; next_bit += 1; terms.append(out)
            m['cells'][name] = {'type': '$eq', 'hide_name': 1, 'attributes': {},
                'parameters': {'A_WIDTH': width, 'B_WIDTH': width, 'Y_WIDTH': 1, 'A_SIGNED': 0, 'B_SIGNED': 0},
                'port_directions': {'A': 'input', 'B': 'input', 'Y': 'output'},
                'connections': {'A': list(bits), 'B': list(format(word, f'0{width}b')[::-1]), 'Y': [out]}}
            new_cells.append(name)
        require(terms, 'Empty theorem domain')
        name = f'$pscorr_domain_lemma_{index}_or'; out = next_bit; next_bit += 1
        require(name not in m['cells'], 'Lemma cell-name collision')
        m['cells'][name] = {'type': '$reduce_or', 'hide_name': 1, 'attributes': {},
            'parameters': {'A_WIDTH': len(terms), 'Y_WIDTH': 1, 'A_SIGNED': 0},
            'port_directions': {'A': 'input', 'Y': 'output'}, 'connections': {'A': terms, 'Y': [out]}}
        new_cells.append(name); name = f'$pscorr_domain_lemma_{index}_assume'
        require(name not in m['cells'], 'Lemma cell-name collision')
        m['cells'][name] = {'type': '$assume', 'hide_name': 1,
            'attributes': {'pscorr_certified_domain_lemma': lemma['name']}, 'parameters': {},
            'port_directions': {'A': 'input', 'EN': 'input'}, 'connections': {'A': [out], 'EN': ['1']}}
        new_cells.append(name)
    return result, new_cells


def import_word_domain_lemmas(certificate_path, original_path, design, image, directory, *,
                             certifier, yosys, zero_fault_data=False, initial_reset=False, timeout=30):
    """Return query-only native JSON plus seven already-proved word assumptions.

    Invoke before adding probes or abstractions. `design` must be the exact
    original or exact certified decoder candidate. The caller remains responsible
    for using the declared immutable-ROM, zero-fault, native-reset harness.
    """
    certificate_path, original_path = Path(certificate_path).resolve(), Path(original_path).resolve()
    require(sys.flags.optimize == 0 and os.environ.get('PYTHONOPTIMIZE', '') in ('', '0'),
            'Certificate replay requires Python assertion checks enabled')
    directory = Path(directory).resolve(); directory.mkdir()
    certificate = read(certificate_path)
    allowed = validate_contract(certificate, image, zero_fault_data=zero_fault_data, initial_reset=initial_reset)
    domain = Path(certificate['domain_summary']).resolve().parent
    dependency_paths = [certificate_path, Path(certifier).resolve(), original_path,
        Path(certificate['native_candidate_json']).resolve(), Path(__file__).resolve(),
        Path(import_decoder.__code__.co_filename).resolve(), Path(certificate['candidate_summary']).resolve(),
        Path(certificate['paired_proof_summary']).resolve()]
    paired = Path(certificate['paired_proof_summary']).resolve().parent
    candidate = Path(certificate['candidate_summary']).resolve().parent
    dependency_paths += [paired/name for name in ('temporal_source.py', 'recheck_source.py', 'proof/proof.json', 'proof/miter.aig')]
    dependency_paths += [candidate/name for name in ('reference.v', 'candidate.v', 'harness.sv')]
    dependency_paths += [Path(name) for name in certificate['proof_log_sha256']]
    dependency_paths += [domain/name for name in ('summary.json', 'prove_domain_source.py', 'data_path.json',
        'harness.sv', 'export.ys', 'symbolized_before_prep.json', 'lowered.json', 'model.smt2', 'base.log', 'induction.log')]
    dependencies = {str(path): digest(path) for path in dependency_paths}
    modified, decoder_record = import_decoder(certificate_path, original_path, image, directory/'certificate_replay',
        certifier=certifier, zero_fault_data=zero_fault_data, initial_reset=initial_reset, timeout=timeout)
    original = read(original_path)
    require(design == original or design == modified, 'Lemma target is neither exact original nor certified decoder design')
    summary = read(domain/'summary.json'); projected = read(domain/'data_path.json')
    require(digest(domain/'summary.json') == certificate['domain_summary_sha256'], 'Domain summary changed')
    require(digest(domain/'data_path.json') == certificate['domain_projection_json_sha256'], 'Domain projection changed')
    require(summary['domain'] == 'program_alphabet' and summary['external_word_premise_guard'] == 'rst_ni && instr_rvalid_i',
            'Unqualified external domain premise')
    check_unbounded_domain_proof(summary, domain)
    lemmas = native_lemma_bindings(original, design, projected, summary['projection'])
    # Reconstruct the entire immutable theorem harness. This rules out extra
    # assumptions hidden behind a matching assertion count or a renamed signal.
    ports = projected['modules']['InstructionDataPath']['ports']
    inputs = [f'input [{len(p["bits"])-1}:0] {n}' for n, p in ports.items() if p['direction'] == 'input']
    outputs = [n for n, p in ports.items() if p['direction'] == 'output']
    lines = ['module DomainProof('+', '.join(inputs)+');']
    lines += [f'wire [31:0] {name};' for name in outputs]
    lines += ['InstructionDataPath dut('+', '.join(f'.{name}({name})' for name in ports)+');',
              'always @* begin', '  if ($initstate) assume(!rst_ni);',
              '  if (rst_ni && response_valid) assume('+certificate['domain_expression']+');']
    lines += ['  assert('+certificate['domain_expression'].replace('instruction_i', name)+');' for name in outputs]
    expected = '\n'.join(lines+['end', 'endmodule', ''])
    require((domain/'harness.sv').read_text() == expected, 'Theorem harness has altered premises or observations')
    lowering = replay_domain_export(domain, directory/'domain_export_replay', yosys, timeout)
    lowered = read(domain/'lowered.json')['modules']['DomainProof']
    require(not any(bit in ('x', 'z') for cell in lowered['cells'].values() for bs in cell['connections'].values() for bit in bs),
            'Literal undefined value remains in theorem model')
    counts = {kind: sum(c['type'] == '$'+kind for c in lowered['cells'].values()) for kind in ('assert', 'assume', 'cover')}
    require(counts == {'assert': 7, 'assume': 2, 'cover': 0}, 'Unexpected theorem model property set')
    result, added = _add_domain_assumptions(design, lemmas, allowed)
    for path, expected_hash in dependencies.items():
        require(digest(Path(path)) == expected_hash, 'Proof dependency changed during import: '+path)
    record = {'status': 'seven_proved_native_word_domains_imported', 'accepted_optimization': False,
        'query_only': True, 'new_unproved_internal_premises': 0, 'assumptions_added': len(lemmas),
        'lemma_scope': 'Six native stored instruction words and original decoder input; no occupancy/readiness/tag facts',
        'lemmas': lemmas, 'allowed_words': [f'{value:08x}' for value in sorted(allowed)],
        'added_cells': added, 'original_cells_ports_and_netnames_unchanged': True,
        'target_design': 'original' if design == original else 'certified_decoder_candidate',
        'certificate_replay': decoder_record, 'domain_export_replay': lowering,
        'proof_dependencies_sha256': dependencies, 'proved_domain_model_properties': counts,
        'source_projection_data_cells': sorted(summary['projection']['original_cell_slices']),
        'source_projection_preserved_control_cells': summary['projection']['retained_spill_write_control_cells'],
        'external_premises': certificate['external_premises'], 'rom_image_sha256': image['image_sha256'],
        'composition': 'Under initial native reset and the reset-qualified valid-response word domain, base plus induction proves all seven word domains on an overapproximation of original native transitions. Exact original data/control bindings transfer these theorems to the original core; decoder equivalence preserves this outside-decoder state. The immutable zero-fault ROM harness implies the external premise. Adding these already-proved conclusions therefore removes no reachable behavior and can strengthen an unbounded admission proof without adding a new environmental restriction.'}
    (directory/'importer_source.py').write_bytes(Path(__file__).read_bytes())
    (directory/'summary.json').write_text(json.dumps(record, indent=2)+'\n')
    return result, record


def verify_dependencies(record):
    """Call after a long query: changed evidence invalidates the query result."""
    for path, expected in record['proof_dependencies_sha256'].items():
        require(digest(Path(path)) == expected, 'Imported theorem dependency changed: '+path)
