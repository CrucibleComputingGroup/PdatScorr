#!/usr/bin/env python3
"""Read-only structural audit; no Yosys/SAT/SMT/PDR invocation."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
APP = HERE.parents[1]
REPO = APP.parents[3]
sys.path[:0] = [str(REPO), str(APP)]
import abstract_datapath as abstraction
import domain_lemmas as lemmas


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def main():
    certificate_path = APP.parent / 'isa_baseline/results/program_alphabet_certificate_v3.json'
    certificate = read(certificate_path)
    original_path = Path(certificate['native_original_json'])
    candidate_path = Path(certificate['native_candidate_json'])
    domain_summary = Path(certificate['domain_summary'])
    projection_path = domain_summary.parent / 'data_path.json'
    rom_proof = APP / 'evidence/rom_domain_v2/summary.json'
    paths = {
        'audit_source': Path(__file__), 'abstraction_helper': Path(abstraction.__file__),
        'domain_import_helper': Path(lemmas.__file__),
        'decoder_import_helper': APP / 'certified_decoder.py',
        'decoder_certificate': certificate_path, 'native_original': original_path,
        'native_candidate': candidate_path, 'domain_summary': domain_summary,
        'domain_projection': projection_path, 'external_rom_proof': rom_proof,
    }
    bindings = {name: {'path': str(path.resolve()), 'sha256': sha(path)} for name, path in paths.items()}
    assert bindings['native_original']['sha256'] == certificate['native_original_sha256']
    assert bindings['native_candidate']['sha256'] == certificate['native_candidate_sha256']
    assert bindings['domain_summary']['sha256'] == certificate['domain_summary_sha256']
    assert bindings['domain_projection']['sha256'] == certificate['domain_projection_json_sha256']
    original, candidate = read(original_path), read(candidate_path)
    projected, summary = read(projection_path), read(domain_summary)
    words = {int(word, 16) for word in read(rom_proof)['domain_words']}
    native_bindings = lemmas.native_lemma_bindings(original, candidate, projected, summary['projection'])
    with_lemmas, added = lemmas._add_domain_assumptions(candidate, native_bindings, words)
    abstract, audit = abstraction.abstract_datapath(with_lemmas, 'datapath', 'alu_mul')
    abstract_first, plain_audit = abstraction.abstract_datapath(candidate, 'datapath', 'alu_mul')
    commute, _ = lemmas._add_domain_assumptions(abstract_first, native_bindings, words)
    native = candidate['modules']['datapath']; before = with_lemmas['modules']['datapath']; after = abstract['modules']['datapath']
    cuts = set(audit['native_cells_removed'])
    states = {name: cell for name, cell in native['cells'].items() if abstraction._state_cell(cell)}
    projection_cells = set(summary['projection']['original_cell_slices']) | set(summary['projection']['retained_spill_write_control_cells'])
    assert cuts == {'$procmux$11115', '$procmux$7848'}
    assert audit['fresh_symbolic_bits_per_cycle'] == 128
    assert abstract == commute and not cuts & projection_cells and not cuts & set(added)
    assert all(after['cells'][name] == cell for name, cell in states.items())
    assert all(after['cells'][name] == cell for name, cell in before['cells'].items() if name not in cuts)
    assert all(after[key] == before[key] for key in before if key != 'cells')
    assert sum(after['cells'][name]['type'] == '$assume' for name in added) == 7
    for name, path in paths.items():
        assert sha(path) == bindings[name]['sha256'], f'Source changed during audit: {name}'
    consumer_summary = {}
    for cut in audit['cuts']:
        bits = set(cut['output_bits']); consumers = []
        for name, cell in native['cells'].items():
            pins = {pin: len(bits & set(values)) for pin, values in cell['connections'].items()
                    if cell['port_directions'][pin] == 'input' and bits & set(values)}
            if pins:
                consumers.append({'cell': name, 'type': cell['type'], 'input_pins': pins,
                                  'source': cell.get('attributes', {}).get('src')})
        assert all(set(c['input_pins']) == {'B'} and c['input_pins']['B'] == 64 for c in consumers)
        consumer_summary[cut['target']] = consumers
    record = {
        'status': 'read_only_structural_and_trace_inclusion_review_passed',
        'new_formal_queries': 0, 'accepted_optimization': False, 'source_bindings': bindings,
        'mode': 'alu_mul', 'fresh_symbolic_bits_per_cycle': 128,
        'native_cells': len(native['cells']), 'native_state_cells': len(states),
        'unchanged_native_cells': len(native['cells']) - len(cuts),
        'native_state_canonical_sha256': abstraction.canonical_hash(states),
        'added_lemma_encoding_cells': len(added), 'lemma_assumptions': 7,
        'all_native_state_and_connections_unchanged': True,
        'all_lemma_encoding_cells_unchanged': True, 'ports_netnames_and_module_attributes_unchanged': True,
        'certified_projection_overlap': [], 'commutes_with_lemma_addition': True,
        'native_candidate_structural_sha256': plain_audit['original_structural_sha256'],
        'abstract_with_lemmas_structural_sha256': audit['abstract_structural_sha256'],
        'cuts': audit['cuts'], 'direct_consumers': consumer_summary,
        'argument': 'The certified decoder substitution preserves original constrained behavior. All seven source-bound word domains hold on those original traces once the exact Harvard producer theorem closes the external premise. For each such trace choose both fresh anyseq outputs equal to their removed combinational driver values at every step, retaining the same prestate and external inputs. Every remaining equation, next-state assignment, property, and imported lemma then has its original value. Therefore the abstraction restricted by these already-proved lemmas still contains every original constrained trace; a universal safety proof transfers back. An abstract counterexample may be spurious.',
        'limits': [
            'This is a structural transformation audit plus trace-inclusion argument, not a new solver proof.',
            'No occupancy, fairness, readiness, latency, branch-outcome, or instruction assumption is added by the abstraction.',
            'Handshake/tag/latency equations and native state are structurally retained; arbitrary payloads can indirectly change later addresses, branches, recovery, and control behavior.',
            'Only alu_mul was reviewed for this composition. The optional branch_taken mode was not used.',
            'The current combined query integration must import and validate native certificates before abstraction; keep the unabstracted hardware export separate and preserve the original strict admission assertion.',
            'Keep anyseq symbolic through the safe JSON formal frontend. Do not map or credit this proof-only model as an implementation or area saving.',
        ],
    }
    (HERE / 'summary.json').write_text(json.dumps(record, indent=2) + '\n')
    snapshots = HERE / 'sources'; snapshots.mkdir(exist_ok=True)
    for name in ['abstraction_helper', 'domain_import_helper', 'decoder_import_helper',
                 'decoder_certificate', 'domain_summary', 'domain_projection', 'external_rom_proof']:
        path = paths[name]
        (snapshots / (name + path.suffix)).write_bytes(path.read_bytes())
    print(json.dumps({key: record[key] for key in ['status', 'native_cells', 'native_state_cells',
        'unchanged_native_cells', 'added_lemma_encoding_cells', 'lemma_assumptions', 'commutes_with_lemma_addition']}))


if __name__ == '__main__':
    main()
