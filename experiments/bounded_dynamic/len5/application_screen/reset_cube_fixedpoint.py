#!/usr/bin/env python3
"""Conservative reset-word fixed point, followed by joint SAT certification.

Native target safety solving and physical mapping are not performed. Structural
descent may discard true facts. Only the final reset-base and simultaneous
one-step induction proof can authorize a separate query-only constant patch.
"""
import argparse
import copy
import json
from pathlib import Path
import time

import reset_cube
from reset_cube import digest, eligibility, prepare, project, read, require


def patch_constants(design, top, rows):
    result = copy.deepcopy(design)
    module = result['modules'][top]
    constants = {bit: value for row in rows for bit, value in zip(row['q'], row['reset_value'])}
    removed = []
    for row in rows:
        name = row['name']
        require(module['cells'][name] == row['cell'], 'Native FF changed before patch')
        require(not any('init' in n.get('attributes', {}) and set(n['bits']) & set(row['q'])
                        for n in module['netnames'].values()), 'Selected native initialization attribute unsupported')
        del module['cells'][name]
        removed.append(name)
    for cell in module['cells'].values():
        for pin, direction in cell['port_directions'].items():
            if direction == 'input':
                cell['connections'][pin] = [constants.get(bit, bit) for bit in cell['connections'][pin]]
            else:
                require(not set(cell['connections'][pin]) & set(constants), 'Selected constant retains a source driver')
    for collection in ('ports', 'netnames'):
        for item in module[collection].values():
            item['bits'] = [constants.get(bit, bit) for bit in item['bits']]
    return result, {'constant_substitutions': constants, 'removed_whole_ff_cells': removed}


def audit_patch(original, modified, top, audit):
    """Check all original graph objects and connections against exact constants."""
    a, b = original['modules'][top], modified['modules'][top]
    constants = audit['constant_substitutions']
    require(set(a['cells'])-set(b['cells']) == set(audit['removed_whole_ff_cells']) and
            not set(b['cells'])-set(a['cells']), 'Unexpected patch cell set')
    for name, cell in b['cells'].items():
        before = a['cells'][name]
        require({k: v for k, v in before.items() if k != 'connections'} ==
                {k: v for k, v in cell.items() if k != 'connections'}, 'Nonconnection native cell mutation')
        for pin, bits in before['connections'].items():
            expected = [constants.get(bit, bit) for bit in bits] if before['port_directions'][pin] == 'input' else bits
            require(cell['connections'][pin] == expected, 'Unexpected native input/output connection mutation')
    for collection in ('ports', 'netnames'):
        require(set(a[collection]) == set(b[collection]), 'Changed native alias/port inventory')
        for name, item in a[collection].items():
            expected = dict(item, bits=[constants.get(bit, bit) for bit in item['bits']])
            require(b[collection][name] == expected, 'Unexpected native alias/port mutation')
    for key in set(a) | set(b):
        if key not in ('cells', 'ports', 'netnames'):
            require(a.get(key) == b.get(key), 'Changed native memory or module metadata')
    return {'exact_graph_audit': True, 'whole_ff_words_removed': len(audit['removed_whole_ff_cells']),
            'constant_bits': len(constants), 'all_other_cell_functions_preserved': True,
            'native_memories_preserved': True, 'formal_cells_added': 0}


def run(design, top, output, *, yosys, max_rounds=100, seconds=600, proof_seconds=120, dependencies=None):
    start = time.monotonic()
    deadline = start + seconds
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    dependencies = dict(dependencies or {})
    for path in (Path(__file__), Path(reset_cube.__file__), Path(yosys)):
        dependencies[str(path.resolve())] = digest(path)
    def verify():
        for path, expected in dependencies.items():
            require(digest(Path(path)) == expected, 'Fixed-point dependency changed: ' + path)
    verify()
    require(0 < max_rounds <= 100 and 0 < seconds <= 600 and 0 < proof_seconds <= 120, 'Unauthorized discovery budget')
    (output/'source.json').write_text(json.dumps(design)+'\n')
    (output/'reset_cube.py').write_bytes(Path(reset_cube.__file__).read_bytes())
    (output/'reset_cube_fixedpoint.py').write_bytes(Path(__file__).read_bytes())
    rows, eligible = eligibility(design, top)
    result = {'status': 'running', 'accepted_optimization': False, 'query_only': True,
              'source_sha256': digest(output/'source.json'), 'dependencies_sha256': dependencies,
              'eligibility': eligible, 'max_rounds': max_rounds, 'overall_seconds_cap': seconds,
              'final_proof_seconds_cap': proof_seconds, 'rounds': [], 'certified_bits': 0,
              'certified_words': 0, 'native_fixed_point': False, 'new_environmental_premises': []}
    def remaining():
        return deadline-time.monotonic()
    def save():
        result['elapsed_seconds'] = time.monotonic()-start
        (output/'summary.json').write_text(json.dumps(result, indent=2)+'\n')
    for index in range(max_rounds):
        if not rows:
            result['status'] = 'empty_cube_no_simplification'
            break
        if remaining() <= 0:
            result['status'] = 'incomplete_budget_no_certificate'
            break
        projection, audit = project(design, top, rows)
        proof = prepare(projection, audit, output/f'round_{index}', yosys=yosys,
                        timeout=min(30, max(0.01, remaining()/2)), solve=False)
        require(proof['status'] in ('prepared_only_no_invariant_certificate', 'unknown'), 'Unexpected structural result')
        if proof['status'] == 'unknown':
            result.update(status='incomplete_preparation_no_certificate', incomplete_preparation=proof)
            break
        constants = proof['initial_cofactor_output_constants']
        kept = [row for row in rows if constants[row['name']] == '0']
        discarded = [row['name'] for row in rows if constants[row['name']] != '0']
        result['rounds'].append({'index': index, 'candidate_words': len(rows), 'candidate_bits': sum(r['width'] for r in rows),
            'kept_words': len(kept), 'discarded_words': discarded, 'cofactor': proof,
            'discard_policy': 'Discard every entire word not proved constant by safe structural simplification; dynamic outputs are not presumed invariant.'})
        save()
        print(json.dumps({'round': index, 'words': len(rows), 'kept': len(kept),
                          'cells': proof['lowered_cells'], 'seconds': round(time.monotonic()-start, 3)}), flush=True)
        if not discarded:
            result['native_fixed_point'] = True
            result['status'] = 'fixed_point_awaiting_certificate'
            break
        rows = kept
    else:
        result['status'] = 'incomplete_iteration_cap_no_certificate'
    if result['status'] == 'fixed_point_awaiting_certificate':
        proof_start = time.monotonic()
        proof_deadline = min(deadline, proof_start+proof_seconds)
        certificates = {}
        for mode in ('induction', 'base'):
            if time.monotonic() >= proof_deadline:
                result['status'] = 'incomplete_final_proof_no_certificate'
                break
            projection, audit = project(design, top, rows, mode=mode)
            # Each preparation has three bounded subprocesses. Divide the
            # remaining phase budget so no single export/SAT can overrun it.
            allowance = max(0.01, (proof_deadline-time.monotonic())/3)
            cert = prepare(projection, audit, output/f'final_{mode}', yosys=yosys, timeout=allowance, solve=True)
            certificates[mode] = cert
            if cert['status'] != 'proved_combinationally':
                result['status'] = 'final_proof_failed_no_certificate'
                break
        result['final_proofs'] = certificates
        result['final_proof_seconds'] = time.monotonic()-proof_start
        if set(certificates) == {'base', 'induction'} and all(c['status'] == 'proved_combinationally' for c in certificates.values()):
            if time.monotonic() >= proof_deadline or remaining() <= 0:
                result['status'] = 'incomplete_budget_no_certificate'
            else:
                verify()
                patched, patch = patch_constants(design, top, rows)
                graph_audit = audit_patch(design, patched, top, patch)
                require(remaining() > 0, 'Budget expired before certifying patch')
                (output/'selected_words.json').write_text(json.dumps(rows, indent=2)+'\n')
                (output/'query_only_patch.json').write_text(json.dumps(patched)+'\n')
                (output/'patch.json').write_text(json.dumps(patch, indent=2)+'\n')
                result.update(status='reset_cube_certified_query_patch_only', certified_words=len(rows),
                    certified_bits=sum(row['width'] for row in rows), graph_audit=graph_audit,
                    query_only_patch_sha256=digest(output/'query_only_patch.json'),
                    theorem='Initial active asynchronous reset establishes every selected native word. Source-bound joint one-step SAT proves the simultaneous cube is closed for arbitrary external inputs and arbitrary other state/memory outputs. Every asynchronous reset event also preserves it. This conclusion inherits the separately bound prior inactive-FU input theorem; it adds no admission or timing premise.')
    verify()
    require(digest(output/'source.json') == result['source_sha256'], 'Fixed-point source snapshot changed')
    save()
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--yosys', type=Path, required=True)
    args = p.parse_args()
    here = Path(__file__).resolve().parent
    review = here/'review/inactive_fu_lemmas_v1/summary.json'
    closed = read(review)
    require(closed['status'] == 'independent_end_to_end_composition_review_passed', 'Prior source theorem is not closed')
    source = Path('/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build/inactive_fu_lemmas_v1/query_only.json')
    require(digest(source) == closed['query_sha256'] == 'bb52d686f974809e0bebd4e2b373414ec9a53af34cff5a6a48d1e5ab2465307b', 'Wrong fixed-point input')
    dependencies = dict(closed['source_sha256'])
    dependencies.update({str(source): digest(source), str(review): digest(review)})
    result = run(read(source), 'datapath', args.output, yosys=args.yosys, dependencies=dependencies)
    print(json.dumps({key: result[key] for key in ('status', 'certified_words', 'certified_bits', 'elapsed_seconds')}))


if __name__ == '__main__':
    main()
