#!/usr/bin/env python3
"""Conditional native-row reset theorem and reset-constant rewrite proposals.

This extracts actual FFs and their combinational update logic. A local theorem
assumes no admission to one row; only a future whole-core theorem can discharge
that premise. Neither a successful local proof nor a proposal accepts hardware.
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[3]))
from odc.temporal import (checked_yosys, digest, formal_lower_command, formal_prepare_command,
    parameter_int, proof_passed, run_command, validate_single_clock, yosys_path)

PREFIX = 'u_backend.u_exec_stage.u_alu_unit.u_arith_rs.'
RESET_FF = {'$adff', '$adffe', '$aldff', '$aldffe'}
CUT_FF = RESET_FF | {'$dff', '$dffe', '$sdff', '$sdffe', '$sdffce'}


def require(condition, message):
    if not condition: raise ValueError(message)


def canonical_sha(design):
    return hashlib.sha256(json.dumps(design, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def input_names(source):
    """Read the real ANSI input declarations; reject ambiguous header forms."""
    text = re.sub(r'/\*.*?\*/|//[^\n]*', '', source, flags=re.S)
    start = re.search(r'\binput\b', text)
    require(start is not None, 'No ANSI input header')
    end = text.find(');', start.start()); require(end >= 0, 'Unterminated ANSI header')
    names = []
    for declaration in text[start.start():end].split(','):
        match = re.fullmatch(r'\s*(input|output|inout)\b(.*?)\b([A-Za-z_]\w*)\s*', declaration, re.S)
        require(match is not None, 'Unsupported ANSI port declaration')
        require(match[1] != 'inout', 'Inout boundary is unsupported')
        if match[1] == 'input': names.append(match[3])
    require(len(names) == len(set(names)) and {'clk_i', 'rst_ni'} <= set(names), 'Missing/duplicate clock or reset inputs')
    return names


def driver_map(module):
    result = {}
    for name, cell in module['cells'].items():
        for pin, direction in cell['port_directions'].items():
            if direction == 'output':
                for index, bit in enumerate(cell['connections'][pin]):
                    if type(bit) is int:
                        require(bit not in result, 'Multiple native drivers')
                        result[bit] = (name, pin, index)
    return result


def slice_reset_ff(cell, indices):
    """Slice every width-dependent reset/data port and parameter exactly."""
    require(cell['type'] in RESET_FF, 'Unsupported selected FF type')
    require(indices == sorted(set(indices)) and indices, 'Invalid FF slice indices')
    require('init' not in cell.get('attributes', {}), 'Explicit FF initialization is unsupported')
    c = copy.deepcopy(cell); con, par = c['connections'], c['parameters']
    width = parameter_int(par['WIDTH'])
    expected_ports = {'CLK', 'D', 'Q'} | ({'ALOAD', 'AD'} if c['type'].startswith('$ald') else {'ARST'})
    if c['type'].endswith('e'): expected_ports.add('EN')
    expected_parameters = {'WIDTH', 'CLK_POLARITY'} | ({'ALOAD_POLARITY'} if c['type'].startswith('$ald') else {'ARST_POLARITY', 'ARST_VALUE'})
    if c['type'].endswith('e'): expected_parameters.add('EN_POLARITY')
    require(set(par) == expected_parameters, 'Unsupported selected FF parameter shape')
    require(set(con) == expected_ports and len(con['D']) == len(con['Q']) == width,
            'Unsupported selected FF port shape')
    require(all(0 <= i < width for i in indices), 'Out-of-range FF slice')
    if 'AD' in con:
        require(len(con['AD']) == width and all(bit in ('0', '1') for bit in con['AD']), 'Dynamic/undefined asynchronous reset data')
        reset = [con['AD'][i] for i in indices]
        con['AD'] = reset.copy()
    else:
        value = par['ARST_VALUE']
        require(isinstance(value, str) and len(value) == width and set(value) <= {'0', '1'}, 'Undefined or malformed reset value')
        reset = [value[::-1][i] for i in indices]
        par['ARST_VALUE'] = ''.join(reset)[::-1]
    for pin in ('D', 'Q'): con[pin] = [con[pin][i] for i in indices]
    par['WIDTH'] = format(len(indices), '032b')
    return c, reset


def select_row(design, row, *, prefix=PREFIX):
    m = design['modules']['datapath']; nets = m['netnames']; drivers = driver_map(m)
    depth = len(nets[prefix+'empty']['bits'])
    require(depth > 0 and depth & (depth-1) == 0 and 0 <= row < depth, 'Invalid native row/depth')
    fields = {}; bits = []
    for name in ('data', 'curr_state'):
        packed = nets[prefix+name]['bits']; require(len(packed) % depth == 0, 'Packed row width does not divide depth')
        width = len(packed)//depth; selected = packed[row*width:(row+1)*width]
        fields[name] = {'width': width, 'bits': selected}; bits += selected
    require(len(bits) == len(set(bits)), 'Aliased selected row bits are unsupported')
    selected = {}
    for bit in bits:
        if isinstance(bit, str):
            require(bit in ('0', '1'), 'Undefined row alias'); continue
        name, pin, index = drivers[bit]
        require(pin == 'Q' and m['cells'][name]['type'] in RESET_FF, 'Row bit is not supported native FF-Q')
        selected.setdefault(name, []).append(index)
    for net in nets.values():
        if set(net['bits']) & set(bits):
            require('init' not in net.get('attributes', {}), 'Explicit selected-state initialization is unsupported')
    reset_by_bit = {}; sliced = {}; selection = []
    clock, reset = nets[prefix+'clk_i']['bits'], nets[prefix+'rst_ni']['bits']
    for name in sorted(selected):
        indices = sorted(selected[name]); cell, values = slice_reset_ff(m['cells'][name], indices)
        reset_pin = 'ALOAD' if 'AD' in cell['connections'] else 'ARST'
        require(cell['connections']['CLK'] == clock and cell['connections'][reset_pin] == reset and
                parameter_int(cell['parameters']['CLK_POLARITY']) == 1 and
                parameter_int(cell['parameters'][reset_pin+'_POLARITY']) == 0, 'Unsupported native clock/reset domain')
        sliced[name] = cell
        reset_by_bit.update(zip(cell['connections']['Q'], values))
        selection.append({'cell': name, 'indices': indices, 'q_bits': cell['connections']['Q'], 'reset_bits': values})
    reset_bits = [reset_by_bit[bit] if type(bit) is int else bit for bit in bits]
    return sliced, {'row': row, 'depth': depth, 'fields': fields, 'row_bits': bits, 'reset_bits': reset_bits,
                    'selected_ff_slices': selection, 'ff_bits': len(reset_by_bit), 'native_constant_alias_bits': len(bits)-len(reset_by_bit)}


def project_row(design, row, source_header, *, prefix=PREFIX):
    m = design['modules']['datapath']; cells, audit = select_row(design, row, prefix=prefix)
    declarations = re.sub(r'/\*.*?\*/|//[^\n]*', '', source_header, flags=re.S)
    for name in ('data', 'curr_state'):
        require(re.search(r'\[\s*DEPTH\s*-\s*1\s*:\s*0\s*\]\s*'+name+r'\s*[,;]', declarations),
                'Native numeric row order requires descending packed [DEPTH-1:0] '+name)
    drivers = driver_map(m); names = input_names(source_header)
    bindings = {name: list(m['netnames'][prefix+name]['bits']) for name in names}
    clock, reset = bindings['clk_i'], bindings['rst_ni']
    insert, index = m['netnames'][prefix+'insert']['bits'], m['netnames'][prefix+'new_idx']['bits']
    require(len(clock) == len(reset) == len(insert) == 1 and len(index) == (audit['depth']-1).bit_length(), 'Invalid admission/control widths')
    require(all(type(x) is int for x in clock+reset+insert+index), 'Constant admission/clock cutpoint unsupported')
    named = clock+reset+insert+index
    require(len(named) == len(set(named)), 'Named input cutpoints collide')
    boundary = {bit for bs in bindings.values() for bit in bs if type(bit) is int} | set(named)
    selected_q = {bit for item in audit['selected_ff_slices'] for bit in item['q_bits']}
    require(not selected_q & boundary, 'Input cutpoint aliases selected FF-Q')
    primary = {bit for port in m['ports'].values() if port['direction'] == 'input' for bit in port['bits'] if type(bit) is int}
    other_state, primary_cut, visiting = set(), set(), set()
    def visit(bit):
        if type(bit) is not int or bit in boundary or bit in selected_q: return
        if bit in primary: primary_cut.add(bit); return
        require(bit in drivers, 'Undriven native combinational input')
        name, pin, _ = drivers[bit]; original = m['cells'][name]
        if original['type'] in CUT_FF:
            require(pin == 'Q', 'Unexpected sequential cut output')
            other_state.add(bit); return
        require(original['type'].startswith('$') and not any(token in original['type'].lower()
                for token in ('ff', 'latch', 'mem', 'assume', 'assert', 'cover', 'check', 'any', '$sr')),
                'Unsupported combinational fanin primitive: '+original['type'])
        if name in cells: return
        require(name not in visiting, 'Native combinational loop')
        visiting.add(name)
        for port, direction in original['port_directions'].items():
            if direction == 'input':
                for value in original['connections'][port]: visit(value)
        visiting.remove(name); cells[name] = copy.deepcopy(original)
    for cell in list(cells.values()):
        for pin, direction in cell['port_directions'].items():
            if direction == 'input':
                for bit in cell['connections'][pin]: visit(bit)
    driven = {bit for c in cells.values() for pin, direction in c['port_directions'].items()
              if direction == 'output' for bit in c['connections'][pin] if type(bit) is int}
    cuts = boundary | other_state | primary_cut
    require(not driven & cuts, 'Retained native driver collides with an arbitrary input cutpoint')
    ports = {'clk_i': {'direction': 'input', 'bits': clock}, 'rst_ni': {'direction': 'input', 'bits': reset},
             'insert_i': {'direction': 'input', 'bits': insert}, 'new_index_i': {'direction': 'input', 'bits': index}}
    for name, values in [('rs_inputs', boundary-set(named)), ('other_state', other_state), ('native_inputs', primary_cut)]:
        if values: ports[name] = {'direction': 'input', 'bits': sorted(values)}
    input_bits = [bit for p in ports.values() for bit in p['bits']]
    require(len(input_bits) == len(set(input_bits)), 'Input port aliases would create multiple formal drivers')
    ports['row_q'] = {'direction': 'output', 'bits': audit['row_bits']}
    projection = {'modules': {'NativeRow': {'attributes': {'top': '1'}, 'ports': ports, 'cells': cells,
        'netnames': {name: {'bits': p['bits'], 'hide_name': 0, 'attributes': {}} for name, p in ports.items()}}}}
    audit.update(native_design_sha256=canonical_sha(design), source_header_sha256=hashlib.sha256(source_header.encode()).hexdigest(),
        numeric_row_binding='Original packed [DEPTH-1:0] declarations: numeric row0 is the least-significant row slice',
        prefix=prefix, source_input_ports=bindings, insert_bits=insert, index_bits=index,
        arbitrary_other_ff_q_bits=sorted(other_state), arbitrary_native_input_bits=sorted(primary_cut),
        combinational_cells=sorted(set(cells)-{x['cell'] for x in audit['selected_ff_slices']}),
        selected_ff_and_native_combinational_logic_preserved=True)
    return projection, audit


def harness(projection, audit, *, no_admission=True):
    ports = projection['modules']['NativeRow']['ports']; width = len(audit['row_bits'])
    inputs = [f'input [{len(p["bits"])-1}:0] {n}' for n,p in ports.items() if p['direction'] == 'input']
    lines = ['module ResetStorageProof('+', '.join(inputs)+');', f'wire [{width-1}:0] row_q;',
        'NativeRow dut('+', '.join(f'.{n}({n})' for n in ports)+');', 'always @* begin',
        '  if ($initstate) assume(!rst_ni);']
    if no_admission: lines.append(f'  if (rst_ni) assume(!(insert_i && new_index_i == {len(audit["index_bits"])}\'d{audit["row"]}));')
    lines += [f'  assert(row_q == {width}\'b'+''.join(audit['reset_bits'])[::-1]+');', 'end', 'endmodule', '']
    return '\n'.join(lines)


def prove_local(projection, audit, out, *, yosys, smtbmc, timeout=20):
    out.mkdir(); (out/'projection.json').write_text(json.dumps(projection)+'\n')
    record = {'status': 'unproved', 'conditional': True, 'accepted_optimization': False, 'global_premise_discharged': False,
              'projection': audit, 'proofs': {}, 'local_premise': f'initial native reset and rst_ni -> !(insert && new_idx == {audit["row"]})',
              'admission_during_reset_restricted': False}
    for positive in (True, False):
        directory = out/('positive' if positive else 'negative'); directory.mkdir()
        (directory/'harness.sv').write_text(harness(projection, audit, no_admission=positive))
        try:
            model = directory/'model.smt2'
            export = checked_yosys(yosys, f'read_json {yosys_path(out/"projection.json")}\nsetundef -anyseq\n'
                'bwmuxmap\nbmuxmap\ndemuxmap\nsetundef -anyseq\n'
                f'read_verilog -formal -sv {yosys_path(directory/"harness.sv")}\n'+formal_prepare_command('ResetStorageProof')+
                formal_lower_command(yosys)+'async2sync\ndffunmap\nsetundef -anyseq\ncheck -assert\n'+
                f'write_json {yosys_path(directory/"lowered.json")}\nwrite_smt2 -wires {yosys_path(model)}\n', directory, 'export', timeout)
            lowered = json.loads((directory/'lowered.json').read_text()); validate_single_clock(lowered, 'ResetStorageProof')
            require(not any(bit in ('x', 'z') for c in lowered['modules']['ResetStorageProof']['cells'].values()
                            for bs in c['connections'].values() for bit in bs), 'Undefined value survived safe lowering')
            args = [smtbmc, '-s', 'z3', '-t', '4', '--noprogress']
            base = run_command(args+['--dump-vcd', str(directory/'counterexample.vcd'), str(model)], directory/'base.log', timeout)
            result = {'export': export, 'base': base, 'model_sha256': digest(model), 'lowered_sha256': digest(directory/'lowered.json')}
            if positive and proof_passed(base):
                result['induction'] = run_command(args+['-i', str(model)], directory/'induction.log', timeout)
            if positive: result['proven'] = proof_passed(base) and 'induction' in result and proof_passed(result['induction'])
            else:
                log = Path(base['log']).read_text()
                result['counterexample_found'] = (base['returncode'] == 1 and not base['timeout'] and
                    'Status: FAILED' in log and (directory/'counterexample.vcd').exists() and 'ERROR' not in log)
            record['proofs']['positive' if positive else 'negative'] = result
        except (ValueError, RuntimeError, OSError, KeyError) as error:
            record['proofs']['positive' if positive else 'negative'] = {'error': str(error)}
    if record['proofs']['positive'].get('proven') and record['proofs']['negative'].get('counterexample_found'):
        record['status'] = 'conditional_reset_storage_proved'
    paths = [out/'projection.json']+[f for d in (out/'positive',out/'negative') for f in d.iterdir() if f.is_file()]
    record['dependencies_sha256'] = {str(p.resolve()): digest(p) for p in paths}
    (out/'summary.json').write_text(json.dumps(record, indent=2)+'\n')
    return record


def conditional_rewrite(design, records):
    """Generate a proposal only. No global admission theorem is presumed."""
    native_hash = canonical_sha(design); module = design['modules']['datapath']; drivers = driver_map(module)
    replacements, selected = {}, {}
    for record in records:
        require(record['status'] == 'conditional_reset_storage_proved' and record['proofs']['positive']['proven'] and
                record['proofs']['negative']['counterexample_found'], 'Missing qualified conditional local theorem')
        positive = record['proofs']['positive']
        require('base' in positive and 'induction' in positive and
                proof_passed(positive['base']) and proof_passed(positive['induction']) and
                '-i' in positive['induction']['argv'] and '-i' not in positive['base']['argv'],
                'A bounded pass or synthetic status cannot qualify a conditional theorem')
        require(record['projection']['native_design_sha256'] == native_hash, 'Conditional theorem belongs to different native RTL')
        for path, sha in record['dependencies_sha256'].items(): require(digest(Path(path)) == sha, 'Local proof evidence changed')
        _, fresh = select_row(design, record['projection']['row'], prefix=record['projection']['prefix'])
        require(fresh['selected_ff_slices'] == record['projection']['selected_ff_slices'], 'Theorem FF binding changed')
        for item in fresh['selected_ff_slices']:
            for index, bit, value in zip(item['indices'], item['q_bits'], item['reset_bits']):
                require(drivers[bit] == (item['cell'], 'Q', index), 'Rewrite Q driver mismatch')
                require(bit not in replacements, 'Overlapping conditional row rewrites')
                replacements[bit] = value; selected.setdefault(item['cell'], set()).add(index)
    require(replacements, 'Empty rewrite proposal')
    require(not set(replacements) & {bit for p in module['ports'].values() if p['direction']=='input' for bit in p['bits']},
            'Cannot replace hardware input drivers')
    out = copy.deepcopy(design); changed = out['modules']['datapath']; deleted = []; sliced = []
    for name, removed in selected.items():
        remaining = [i for i in range(len(changed['cells'][name]['connections']['Q'])) if i not in removed]
        if not remaining: del changed['cells'][name]; deleted.append(name)
        else:
            changed['cells'][name], _ = slice_reset_ff(changed['cells'][name], remaining); sliced.append(name)
    for cell in changed['cells'].values():
        for pin, direction in cell['port_directions'].items():
            if direction == 'input': cell['connections'][pin] = [replacements.get(x,x) for x in cell['connections'][pin]]
            else: require(not set(cell['connections'][pin]) & set(replacements), 'Replacement leaves a second native driver')
    for named in [changed['ports'], changed['netnames']]:
        for net in named.values(): net['bits'] = [replacements.get(x,x) for x in net['bits']]
    return out, {'status': 'conditional_proposal_only', 'accepted_optimization': False, 'global_premise_discharged': False,
        'native_design_sha256': native_hash, 'proposal_design_sha256': canonical_sha(out),
        'required_no_admission_rows': [r['projection']['row'] for r in records],
        'reset_constant_bits': len(replacements), 'deleted_native_ff_cells': deleted, 'sliced_native_ff_cells': sliced,
        'constant_substitutions': {str(k): v for k,v in sorted(replacements.items())},
        'native_parameters_and_capacity_alias_widths_unchanged': True,
        'condition': 'Requires future unbounded original-core rst_ni -> no-admission proof for every listed row under the exact main environment; local component proofs alone authorize no hardware acceptance or area claim.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, required=True); parser.add_argument('--rs-source', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True); parser.add_argument('--yosys', required=True)
    parser.add_argument('--rows', type=int, nargs='+'); parser.add_argument('--timeout', type=int, default=20)
    args = parser.parse_args(); out=args.output.resolve(); out.mkdir(parents=True, exist_ok=False)
    design=json.loads(args.source.read_text()); header=args.rs_source.read_text()
    dependencies={str(p.resolve()):digest(p) for p in (args.source,args.rs_source,Path(__file__))}
    (out/'reset_storage_source.py').write_bytes(Path(__file__).read_bytes()); (out/'arith_rs_source.sv').write_text(header)
    depth=len(design['modules']['datapath']['netnames'][PREFIX+'empty']['bits']); rows=args.rows or list(range(depth))
    require(len(rows)==len(set(rows)), 'Duplicate row requests'); records=[]; proposals=[]
    for row in rows:
        projection,audit=project_row(design,row,header)
        record=prove_local(projection,audit,out/f'row_{row}',yosys=args.yosys,
            smtbmc=str(Path(args.yosys).with_name('yosys-smtbmc')),timeout=args.timeout)
        records.append(record)
        if record['status']=='conditional_reset_storage_proved':
            _,proposal=conditional_rewrite(design,[record]);proposals.append(proposal)
            (out/f'row_{row}'/'conditional_patch.json').write_text(json.dumps(proposal,indent=2)+'\n')
        print(json.dumps({'row':row,'status':record['status'],'native_ff_bits':audit['ff_bits']}),flush=True)
    require(all(digest(Path(p))==sha for p,sha in dependencies.items()), 'Source changed during local proofs')
    report={'status':'all_conditional_local_theorems_proved' if len(proposals)==len(rows) else 'incomplete',
        'accepted_optimization':False,'global_premise_discharged':False,'source_sha256':dependencies,
        'rows':[{k:r['projection'][k] for k in ('row','depth','ff_bits')}|{'status':r['status']} for r in records],
        'negative_controls':'Each local no-admission premise removed; failures are component counterexamples, not full-core traces.',
        'no_full_core_proposal_or_mapping_emitted':True,'tool_sha256':digest(Path(args.yosys))}
    (out/'summary.json').write_text(json.dumps(report,indent=2)+'\n')
    return 0 if len(proposals)==len(rows) else 1


if __name__=='__main__': raise SystemExit(main())
