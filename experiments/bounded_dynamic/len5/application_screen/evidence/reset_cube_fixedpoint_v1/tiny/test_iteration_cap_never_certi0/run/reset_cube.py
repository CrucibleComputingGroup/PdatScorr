#!/usr/bin/env python3
"""Discover whole-word reset invariants by simultaneous one-step induction.

Standalone proof experiment: no hardware rewrite or admission premise. Other
state outputs are arbitrary, including memory reads. Every selected FF has a
known constant asynchronous reset tied to the declared top clock/reset. A
descending candidate cube is only accepted after source-bound reset-base and
joint combinational SAT induction succeed. Undefined values are made symbolic
before any combinational optimization.
"""
from __future__ import annotations

import argparse
import collections
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import time

SUPPORTED = {'$adff', '$adffe', '$aldff', '$aldffe'}
FORBIDDEN = {'$assert', '$assume', '$cover', '$check', '$initstate', '$live', '$fair'}


def require(value, message):
    if not value:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def integer(value):
    return int(value, 2) if isinstance(value, str) else int(value)


def read(path):
    return json.loads(Path(path).read_text())


def quoted(path):
    value = str(Path(path).resolve())
    require(not any(c in value for c in ('\n', '\r', '"', '\\')), 'Unsupported Yosys path')
    return '"' + value + '"'


def state_cell(cell):
    kind = cell['type'].lower()
    return ('ff' in kind or 'latch' in kind or kind.startswith('$mem') or
            kind in ('$sr', '$_sr_'))


def eligibility(design, top, clock='clk_i', reset='rst_ni', clock_polarity=1, reset_polarity=0):
    require(set(design['modules']) == {top}, 'Expected a single flattened native module')
    module = design['modules'][top]
    for name in (clock, reset):
        port = module['ports'][name]
        require(port['direction'] == 'input' and len(port['bits']) == 1 and
                type(port['bits'][0]) is int, 'Clock/reset must be scalar native inputs')
    inputs = {bit for port in module['ports'].values() if port['direction'] == 'input' for bit in port['bits']}
    drivers = {}
    for name, cell in module['cells'].items():
        require(cell['type'].startswith('$') and cell['type'] not in FORBIDDEN, 'Opaque cell or existing proof premise')
        for pin, direction in cell['port_directions'].items():
            require(direction in ('input', 'output'), 'Bidirectional primitive unsupported')
            if direction == 'output':
                for bit in cell['connections'][pin]:
                    if type(bit) is int:
                        require(bit not in drivers and bit not in inputs, 'Multiple/input driver in native model')
                        drivers[bit] = (name, pin)
    records, rejected = [], {}
    for name, cell in module['cells'].items():
        if not state_cell(cell):
            continue
        def reject(reason):
            rejected[name] = reason
        if cell['type'] not in SUPPORTED:
            reject('Not a supported asynchronously reset FF word')
            continue
        con, par = cell['connections'], cell['parameters']
        if con['CLK'] != module['ports'][clock]['bits'] or integer(par['CLK_POLARITY']) != clock_polarity:
            reject('Different clock or clock polarity')
            continue
        rst_pin = 'ALOAD' if cell['type'].startswith('$ald') else 'ARST'
        if con[rst_pin] != module['ports'][reset]['bits'] or integer(par[rst_pin+'_POLARITY']) != reset_polarity:
            reject('Different reset or reset polarity')
            continue
        q = con['Q']
        value = list(con['AD']) if rst_pin == 'ALOAD' else list(par['ARST_VALUE'][::-1])
        require(integer(par['WIDTH']) == len(q) == len(con['D']) == len(value), 'FF word width differs')
        require(len(set(q)) == len(q) and all(type(bit) is int for bit in q), 'FF Q aliases or constants')
        if not all(bit in ('0', '1') for bit in value):
            reject('Reset is not a fully known constant word')
            continue
        enabled = cell['type'] in ('$adffe', '$aldffe')
        if enabled:
            require(len(con['EN']) == 1 and integer(par['EN_POLARITY']) in (0, 1), 'Malformed native enable')
        records.append({'name': name, 'cell': copy.deepcopy(cell), 'width': len(q),
                        'q': list(q), 'reset_value': value, 'reset_pin': rst_pin,
                        'reset_polarity': reset_polarity, 'clock_polarity': clock_polarity,
                        'enable_polarity': integer(par['EN_POLARITY']) if enabled else None})
    records.sort(key=lambda r: r['name'])
    return records, {'top': top, 'clock': clock, 'reset': reset, 'clock_polarity': clock_polarity,
                     'reset_polarity': reset_polarity, 'eligible_words': len(records),
                     'eligible_bits': sum(r['width'] for r in records), 'rejected_state_cells': rejected,
                     'native_memory_arrays': len(module.get('memories', {}))}


def project(design, top, candidates, *, clock='clk_i', reset='rst_ni', mode='induction'):
    """Faithful FF reset/enable adapters around an overapproximated native cone."""
    require(mode in ('base', 'induction'), 'Unknown obligation')
    original = design['modules'][top]
    module = copy.deepcopy(original)
    module['attributes'] = {'top': '1'}
    module['ports'] = {n: copy.deepcopy(p) for n, p in original['ports'].items() if p['direction'] == 'input'}
    module['netnames'] = {}
    # Every other state output is an arbitrary shared current value. Cutting a
    # whole memory's outputs overapproximates all its read/write histories.
    module['memories'] = {}
    all_bits = [bit for cell in original['cells'].values() for bits in cell['connections'].values()
                for bit in bits if type(bit) is int]
    all_bits += [bit for port in original['ports'].values() for bit in port['bits'] if type(bit) is int]
    next_bit = max(all_bits, default=1) + 1
    replacements = {bit: value for row in candidates for bit, value in zip(row['q'], row['reset_value'])} if mode == 'induction' else {}
    cuts = []
    for name, cell in list(module['cells'].items()):
        if not state_cell(cell):
            continue
        del module['cells'][name]
        for pin, direction in cell['port_directions'].items():
            if direction != 'output':
                continue
            bits = list(cell['connections'][pin])
            require(all(type(bit) is int for bit in bits), 'Non-wire state output')
            free = [bit for bit in bits if bit not in replacements]
            if free:
                port = f'free_state_{len(cuts)}'
                require(port not in module['ports'], 'Free-state port collision')
                module['ports'][port] = {'direction': 'input', 'bits': free}
                cuts.append({'native_cell': name, 'native_port': pin, 'bits': free, 'port': port})
    for cell in module['cells'].values():
        for pin, direction in cell['port_directions'].items():
            if direction == 'input':
                cell['connections'][pin] = [replacements.get(bit, bit) for bit in cell['connections'][pin]]
    def wire(width):
        nonlocal next_bit
        value = list(range(next_bit, next_bit+width))
        next_bit += width
        return value
    serial = 0
    def cell(kind, connections, parameters, outputs=('Y',)):
        nonlocal serial
        name = f'$reset_cube_adapter_{serial}'
        serial += 1
        require(name not in module['cells'], 'Adapter cell-name collision')
        module['cells'][name] = {'hide_name': 1, 'type': kind, 'attributes': {},
            'parameters': parameters, 'connections': connections,
            'port_directions': {pin: 'output' if pin in outputs else 'input' for pin in connections}}
    def mux(a, b, select):
        require(len(a) == len(b) and len(select) == 1, 'Invalid mux adapter')
        out = wire(len(a))
        cell('$mux', {'A': a, 'B': b, 'S': select, 'Y': out}, {'WIDTH': len(a)})
        return out
    bads, observations = [], []
    for index, row in enumerate(candidates):
        con = row['cell']['connections']
        value = row['reset_value']
        current = [replacements.get(bit, bit) for bit in row['q']]
        if mode == 'base':
            normal = current
        else:
            normal = [replacements.get(bit, bit) for bit in con['D']]
            if row['enable_polarity'] is not None:
                enable = [replacements.get(bit, bit) for bit in con['EN']]
                normal = mux(current, normal, enable) if row['enable_polarity'] else mux(normal, current, enable)
        rst = list(con[row['reset_pin']])
        observed = mux(normal, value, rst) if row['reset_polarity'] else mux(value, normal, rst)
        bad = wire(1)
        cell('$ne', {'A': observed, 'B': value, 'Y': bad},
             {'A_WIDTH': row['width'], 'B_WIDTH': row['width'], 'Y_WIDTH': 1, 'A_SIGNED': 0, 'B_SIGNED': 0})
        port = f'bad_{index}'
        module['ports'][port] = {'direction': 'output', 'bits': bad}
        observations.append({'port': port, 'candidate': row['name'], 'native_q': row['q'], 'width': row['width']})
        bads += bad
    require(bads, 'Empty cube has no proof obligation')
    all_bad = wire(1)
    cell('$reduce_or', {'A': bads, 'Y': all_bad}, {'A_WIDTH': len(bads), 'Y_WIDTH': 1, 'A_SIGNED': 0})
    module['ports']['cube_bad'] = {'direction': 'output', 'bits': all_bad}
    for name, port in module['ports'].items():
        module['netnames'][name] = {'hide_name': 0, 'attributes': {}, 'bits': list(port['bits'])}
    return {'modules': {'ResetCube': module}}, {'mode': mode, 'candidate_words': len(candidates),
        'candidate_bits': sum(r['width'] for r in candidates), 'hypothesis_q_constants': replacements,
        'arbitrary_other_state_outputs': cuts, 'observations': observations,
        'reset_base_premise': {reset: candidates[0]['reset_polarity']} if mode == 'base' else None,
        'transition': 'Reset overrides enable; otherwise source D updates when native enable is active and source Q holds when inactive. Base observes reset-visible native Q. All clocks/resets/polarities and constant reset words are bound to original cells.'}


def execute(script, directory, yosys, timeout):
    directory.mkdir(parents=True, exist_ok=False)
    path = directory/'run.ys'
    path.write_text(script)
    start = time.monotonic()
    try:
        result = subprocess.run([str(yosys), '-Q', '-T', '-s', str(path)], capture_output=True, text=True, timeout=timeout)
        output, code, expired = result.stdout+result.stderr, result.returncode, False
    except subprocess.TimeoutExpired as error:
        output = (error.stdout or b'') + (error.stderr or b'')
        output = output.decode(errors='replace') if isinstance(output, bytes) else output
        code, expired = None, True
    (directory/'run.log').write_text(output)
    return {'argv': [str(yosys), '-Q', '-T', '-s', str(path)], 'returncode': code, 'timeout': expired,
            'seconds': time.monotonic()-start, 'script_sha256': digest(path), 'log_sha256': digest(directory/'run.log')}


def expose_choices(design):
    """Represent symbolic values as arbitrary binary inputs in one-step SAT.

    Yosys SAT can report formal $anyseq cells as undefined. Removing their sole
    driver and exposing the same bits as inputs preserves every binary choice;
    no value is fixed. A constant choice is also safely generalized in this
    one-step overapproximation. No native state transition is altered here.
    """
    result = copy.deepcopy(design)
    module = result['modules']['ResetCube']
    records = []
    for name, cell in list(module['cells'].items()):
        if cell['type'] not in ('$anyseq', '$anyconst'):
            continue
        require(cell['port_directions'] == {'Y': 'output'}, 'Unsupported symbolic-value primitive')
        bits = cell['connections']['Y']
        require(all(type(bit) is int for bit in bits), 'Non-wire symbolic output')
        port = f'free_choice_{len(records)}'
        while port in module['ports']:
            port += '_'
        module['ports'][port] = {'direction': 'input', 'bits': list(bits)}
        module['netnames'][port] = {'hide_name': 0, 'attributes': {}, 'bits': list(bits)}
        del module['cells'][name]
        records.append({'original_cell': name, 'type': cell['type'], 'bits': bits, 'input_port': port})
    return result, records


def prepare(projection, audit, directory, *, yosys, timeout=30, solve=True):
    directory = Path(directory).resolve()
    directory.mkdir(parents=True, exist_ok=False)
    source = directory/'projection.json'
    source.write_text(json.dumps(projection)+'\n')
    (directory/'projection_audit.json').write_text(json.dumps(audit, indent=2)+'\n')
    script = f'read_json {quoted(source)}\nsetundef -anyseq\nbwmuxmap\nbmuxmap\ndemuxmap\nsetundef -anyseq\n'
    script += f'write_json {quoted(directory/"symbolized_before_prep.json")}\n'
    symbolized = execute(script, directory/'symbolize', yosys, timeout)
    result = {'symbolize_execution': symbolized, 'projection_sha256': digest(source), 'new_environmental_premises': [],
              'source_cell_adapter_semantics': audit['transition'], 'status': 'unknown'}
    if symbolized['returncode'] != 0 or symbolized['timeout']:
        return result
    binary, choices = expose_choices(read(directory/'symbolized_before_prep.json'))
    (directory/'binary_inputs_before_prep.json').write_text(json.dumps(binary)+'\n')
    script = f'read_json {quoted(directory/"binary_inputs_before_prep.json")}\nprep -top ResetCube\nsetundef -anyseq\ncheck -assert\n'
    script += f'write_json {quoted(directory/"normalized_symbolic.json")}\n'
    execution = execute(script, directory/'execution', yosys, timeout)
    result['execution'] = execution
    if execution['returncode'] != 0 or execution['timeout']:
        return result
    final, final_choices = expose_choices(read(directory/'normalized_symbolic.json'))
    (directory/'lowered.json').write_text(json.dumps(final)+'\n')
    result['binary_choice_exposure'] = {'before_prep': choices, 'after_prep': final_choices,
        'semantics': 'Every symbolic output becomes a fresh unrestricted binary top input. No symbolic value is fixed or omitted.'}
    lowered = read(directory/'lowered.json')['modules']['ResetCube']
    require(not any(state_cell(c) for c in lowered['cells'].values()), 'State survived one-step projection')
    require(not any(bit in ('x', 'z') for c in lowered['cells'].values() for bs in c['connections'].values() for bit in bs), 'Undefined literal survived preparation')
    require(not any(c['type'] in FORBIDDEN for c in lowered['cells'].values()), 'Hidden proof premise')
    result.update(lowered_sha256=digest(directory/'lowered.json'), lowered_cells=len(lowered['cells']),
                  lowered_cell_types=dict(collections.Counter(c['type'] for c in lowered['cells'].values())),
                  lowered_input_bits=sum(len(p['bits']) for p in lowered['ports'].values() if p['direction']=='input'),
                  initial_cofactor_output_constants={item['candidate']: lowered['ports'][item['port']]['bits'][0]
                      for item in audit['observations']})
    if not solve:
        result['status'] = 'prepared_only_no_invariant_certificate'
        return result
    reset_arg = ''.join(f' -set {name} {value}' for name, value in (audit['reset_base_premise'] or {}).items())
    script = f'read_json {quoted(directory/"lowered.json")}\ncheck -assert\n'
    script += f'tee -o {quoted(directory/"sat.log")} sat -set-def-inputs{reset_arg} -prove cube_bad 0 -show-ports -dump_json {quoted(directory/"counterexample.json")}\n'
    sat = execute(script, directory/'sat_execution', yosys, timeout)
    result['sat_execution'] = sat
    if sat['returncode'] != 0 or sat['timeout']:
        return result
    log = (directory/'sat.log').read_text()
    result['sat_log_sha256'] = digest(directory/'sat.log')
    success = 'SAT proof finished - no model found: SUCCESS!' in log
    failure = 'SAT proof finished - model found: FAIL!' in log
    require(success != failure, 'Missing or contradictory SAT result')
    result['status'] = 'proved_combinationally' if success else 'counterexample'
    if failure:
        witness = read(directory/'counterexample.json')
        values = {}
        for signal in witness['signal']:
            name = signal['name'].lstrip('\\')
            if name.startswith('bad_'):
                wave = signal['wave']
                require(wave[0] in '01', 'Undefined/nonboolean counterexample observation')
                values[name] = int(wave[0])
        require(set(values) == {item['port'] for item in audit['observations']}, 'Counterexample omits candidate outputs')
        result['refuted_words'] = [item['candidate'] for item in audit['observations'] if values[item['port']]]
        require(result['refuted_words'], 'Counterexample does not refute a candidate')
        result['counterexample_sha256'] = digest(directory/'counterexample.json')
    return result


def discover(design, top, directory, *, yosys, clock='clk_i', reset='rst_ni', timeout=30, prepare_only=False):
    directory = Path(directory).resolve()
    directory.mkdir(parents=True, exist_ok=False)
    source = directory/'source.json'
    source.write_text(json.dumps(design)+'\n')
    source_hash = digest(source)
    candidates, eligibility_audit = eligibility(design, top, clock=clock, reset=reset)
    (directory/'eligible.json').write_text(json.dumps(candidates, indent=2)+'\n')
    rows, rounds = list(candidates), []
    result = {'status': 'running', 'query_only': True, 'accepted_optimization': False,
              'input_sha256': source_hash, 'runner_sha256': digest(Path(__file__)), 'yosys_sha256': digest(yosys),
              'eligibility': eligibility_audit, 'rounds': rounds, 'selected_words': [], 'selected_bits': 0,
              'scope': 'Reset-conditioned whole-word constant facts; no timing, occupancy, readiness, program-order or admission premise.'}
    while rows:
        projection, audit = project(design, top, rows, clock=clock, reset=reset, mode='induction')
        proof = prepare(projection, audit, directory/f'round_{len(rounds)}', yosys=yosys, timeout=timeout, solve=not prepare_only)
        rounds.append({'candidate_words': len(rows), 'candidate_bits': sum(r['width'] for r in rows), 'proof': proof})
        if prepare_only:
            result['status'] = proof['status']
            break
        if proof['status'] == 'unknown':
            result['status'] = 'unknown_no_invariant_certificate'
            break
        if proof['status'] == 'proved_combinationally':
            base_projection, base_audit = project(design, top, rows, clock=clock, reset=reset, mode='base')
            base = prepare(base_projection, base_audit, directory/'base', yosys=yosys, timeout=timeout)
            result['base'] = base
            require(base['status'] == 'proved_combinationally', 'Reset base did not prove')
            result.update(status='reset_cube_proved', selected_words=rows, selected_bits=sum(r['width'] for r in rows),
                          final_induction_round=len(rounds)-1,
                          theorem='Initial active native asynchronous reset establishes every selected word. Joint next-state closure under the simultaneous current-state cube holds for arbitrary external inputs and arbitrary other state outputs. Thus induction proves the selected native visible reset constants for all subsequent clock steps; asynchronous reset events also preserve the cube.')
            break
        rejected = set(proof['refuted_words'])
        rows = [row for row in rows if row['name'] not in rejected]
    else:
        result['status'] = 'empty_cube_no_simplification'
    require(digest(source) == source_hash and digest(Path(__file__)) == result['runner_sha256'], 'Discovery source changed')
    (directory/'summary.json').write_text(json.dumps(result, indent=2)+'\n')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--top', default='datapath')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--yosys', required=True)
    parser.add_argument('--prepare-only', action='store_true')
    parser.add_argument('--timeout', type=int, default=30)
    args = parser.parse_args()
    source_hash = digest(args.input)
    result = discover(read(args.input), args.top, args.output, yosys=args.yosys,
                      timeout=args.timeout, prepare_only=args.prepare_only)
    require(digest(args.input) == source_hash, 'Input source changed')
    result.update(original_input_path=str(args.input.resolve()), original_input_sha256=source_hash)
    (args.output/'summary.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({key: result[key] for key in ('status', 'selected_bits', 'accepted_optimization')}))


if __name__ == '__main__':
    main()
