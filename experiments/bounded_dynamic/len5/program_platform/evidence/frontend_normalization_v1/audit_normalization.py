#!/usr/bin/env python3
"""Compare already-exported native normalization stages; never invoke a solver."""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import shutil


def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()


def stats(module):
    cells = module['cells']
    undef = {name: sum(bits.count('x') for bits in cell['connections'].values())
             for name, cell in cells.items()}
    return {'cells': len(cells), 'wires': len(module['netnames']),
        'cell_types': dict(sorted(Counter(c['type'] for c in cells.values()).items())),
        'cell_connection_literal_x_occurrences': sum(undef.values()),
        'cells_with_literal_x_connections': sum(value > 0 for value in undef.values()),
        'literal_x_occurrences_by_cell_type': {kind: sum(undef[name] for name, c in cells.items() if c['type'] == kind)
            for kind in sorted({c['type'] for c in cells.values()}) if any(undef[name] for name, c in cells.items() if c['type'] == kind)},
        'net_init_attribute_count': sum('init' in net.get('attributes', {}) for net in module['netnames'].values())}


def compare_after_buffer_aliases(before, after):
    parent, constants = {}, {}
    def find(bit):
        parent.setdefault(bit, bit)
        if parent[bit] != bit: parent[bit] = find(parent[bit])
        return parent[bit]
    def union(left, right):
        if isinstance(left, str) and isinstance(right, str):
            assert left == right; return
        if isinstance(left, str): left, right = right, left
        left = find(left)
        if isinstance(right, str):
            assert left not in constants or constants[left] == right
            constants[left] = right; return
        right = find(right)
        if left == right: return
        if left in constants and right in constants: assert constants[left] == constants[right]
        parent[right] = left
        if right in constants: constants[left] = constants.pop(right)
    for cell in before['cells'].values():
        if cell['type'] == '$buf':
            assert len(cell['connections']['A']) == len(cell['connections']['Y'])
            for left, right in zip(cell['connections']['A'], cell['connections']['Y']): union(left, right)
    mapping = {}
    for name, net in before['netnames'].items():
        if name not in after['netnames']: continue
        right = after['netnames'][name]['bits']
        assert len(net['bits']) == len(right)
        for left, rbit in zip(net['bits'], right):
            if isinstance(left, int):
                left = find(left)
                assert left not in mapping or mapping[left] == rbit
                mapping[left] = rbit
    for left, value in constants.items():
        left = find(left)
        assert left not in mapping or mapping[left] == value
        mapping[left] = value
    old, new = before['cells'], after['cells']
    changed, attributes_changed = [], []
    for name in old.keys() & new.keys():
        a, b = old[name], new[name]
        con = {port: [mapping[find(bit)] if isinstance(bit, int) else bit for bit in bits]
               for port, bits in a['connections'].items()}
        if (a['type'] != b['type'] or a['parameters'] != b['parameters']
                or a['port_directions'] != b['port_directions'] or con != b['connections']): changed.append(name)
        if a['attributes'] != b['attributes']: attributes_changed.append(name)
    assert not changed
    removed = sorted(old.keys() - new.keys())
    assert not new.keys() - old.keys()
    return {'surviving_cell_function_changes_after_only_original_buffer_alias_resolution': changed,
        'surviving_cell_attribute_changes': sorted(attributes_changed),
        'alias_mapping_conflicts': 0, 'surviving_connection_bits_without_mapping': 0,
        'removed_cell_types': dict(sorted(Counter(old[n]['type'] for n in removed).items())),
        'removed_cells': removed,
        'removed_state_cells': [{'cell': n, 'type': old[n]['type'], 'width': int(old[n]['parameters']['WIDTH'], 2)}
                                for n in removed if 'ff' in old[n]['type']],
        'removed_cells_with_literal_x': [n for n in removed if any('x' in bits for bits in old[n]['connections'].values())]}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--frontend', type=Path, required=True)
    ap.add_argument('--exports', type=Path, required=True)
    ap.add_argument('--prepare-script', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    f, e, out = args.frontend.resolve(), args.exports.resolve(), args.output.resolve()
    manifest = json.loads((f / 'manifest.json').read_text())
    assert sha(f / 'elaborated.il') == manifest['elaborated_il_sha256']
    assert sha(f / 'normalized.il') == manifest['normalized_il_sha256']
    assert sha(f / 'normalize.ys') == manifest['normalized_structural_check']['script_sha256']
    assert sha(f / 'normalize.log') == manifest['normalized_structural_check']['log_sha256']
    designs = {stage: json.loads((e / (stage + '.json')).read_text()) for stage in ('raw', 'after_expr', 'after_clean')}
    published = json.loads((f / 'normalized.json').read_text())
    assert designs['raw'] == designs['after_expr']
    assert designs['after_clean'] == published
    modules = {name: design['modules']['datapath'] for name, design in designs.items()}
    comparison = compare_after_buffer_aliases(modules['raw'], modules['after_clean'])
    assert stats(modules['raw'])['net_init_attribute_count'] == stats(modules['after_clean'])['net_init_attribute_count'] == 0
    sources = [f/'elaborated.il', f/'normalized.il', f/'normalized.json', f/'normalize.ys', f/'normalize.log',
               f/'manifest.json', args.prepare_script, e/'audit.ys', e/'audit.log',
               *[e/(n+'.json') for n in designs]]
    result = {'status': 'audited', 'scope': 'Declared ordinary normalization of the shared native hardware baseline; no equivalence proof or optimization result',
        'source_commit': manifest['upstream_commit'], 'opt_expr_export_byte_semantics': 'Entire parsed JSON is unchanged',
        'opt_expr_entire_json_equal': True, 'replayed_clean_equals_published_normalized_json': True,
        'statistics': {name: stats(module) for name, module in modules.items()}, 'comparison': comparison,
        'no_surviving_literal_x_concretization_in_audited_normalization': True,
        'undefined_value_metric': 'Literal-x occurrences across cell connection arrays; not unique unknown values, state bits, or information entropy',
        'trusted_boundary': 'Pinned source -> slang elaboration -> declared normalized native baseline. This audit covers only opt_expr/opt_clean after elaboration, not source/frontend semantic equivalence or later proof lowering.',
        'remaining_risk': '81,702 literal-x connection occurrences remain in the normalized baseline. Subsequent proof lowering must preserve the intended nondeterminism; this audit does not validate prep or solver export.',
        'source_sha256': {str(path): sha(path) for path in sources},
        'audit_script_sha256': sha(Path(__file__)),
        'export_command': [manifest['yosys'], '-Q', '-T', '-s', str(e/'audit.ys')],
        'yosys_sha256': manifest['yosys_sha256']}
    out.mkdir(parents=True, exist_ok=True)
    for path in [f/'normalize.ys', f/'normalize.log', f/'manifest.json', args.prepare_script, e/'audit.ys', e/'audit.log']:
        shutil.copyfile(path, out / path.name)
    (out / 'summary.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('status', 'opt_expr_entire_json_equal', 'replayed_clean_equals_published_normalized_json', 'no_surviving_literal_x_concretization_in_audited_normalization')}))


if __name__ == '__main__':
    main()
