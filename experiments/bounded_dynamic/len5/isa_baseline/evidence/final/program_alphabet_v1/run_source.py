#!/usr/bin/env python3
"""Exhaustive scalar controllability baseline, followed by all-output proof.

No candidate is prescribed constant. Both values of every eligible decoder
scalar are checked against the original domain. Rewrites enter native hardware
only after an independent combined two-design equivalence check succeeds.
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
from odc.state_candidates import scalar_constant_candidates, replace_scalar_constant
from odc.temporal import checked_yosys, digest, export_design, formal_lower_command, prove_pair, yosys_path
from prepare_frontend import workspace_root


def main():
    workspace = workspace_root(HERE)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepared', type=Path, required=True)
    parser.add_argument('--domain', choices=('isa_operations', 'program_alphabet'), required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--yosys', default=str(workspace/'tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys'))
    parser.add_argument('--abc', default='/usr/local/bin/abc')
    parser.add_argument('--timeout', type=int, default=180)
    args = parser.parse_args()
    prepared, out = args.prepared.resolve(), args.output.resolve()
    manifest = json.loads((prepared/'manifest.json').read_text())
    assert digest(prepared/'decoder.json') == manifest['decoder_json_sha256']
    assert digest(prepared/'whole_core.json') == manifest['whole_core_json_sha256']
    out.mkdir(parents=True, exist_ok=False)
    design = json.loads((prepared/'decoder.json').read_text())
    candidates = scalar_constant_candidates(design, 'DecoderBase')
    nodes = candidates[::2]
    assert all(candidates[2*i]['cell'] == candidates[2*i+1]['cell'] for i in range(len(nodes)))
    probe = copy.deepcopy(design)
    module = probe['modules']['DecoderBase']
    for i, node in enumerate(nodes):
        name = f'probe_{i:04d}'
        assert name not in module['ports'] and name not in module['netnames']
        module['ports'][name] = {'direction': 'output', 'bits': [node['output_bit']]}
        module['netnames'][name] = {'hide_name': 0, 'attributes': {}, 'bits': [node['output_bit']]}
    export_design(probe, 'DecoderBase', 'DecoderProbe', out/'probe.v', args.yosys, args.timeout)
    expression = manifest['domains'][args.domain]['expression']
    names = [f'probe_{i:04d}' for i in range(len(nodes))]
    wrapper = ['module ConstantProbe(input [31:0] instruction_i, ' + ', '.join('output '+name for name in names) + ');',
               'DecoderProbe dut(.instruction_i(instruction_i), '+', '.join(f'.{name}({name})' for name in names)+');',
               'always @* assume('+expression+');', 'endmodule', '']
    (out/'probe_harness.sv').write_text('\n'.join(wrapper))
    script = f'read_verilog -formal -sv {yosys_path(out/"probe.v")} {yosys_path(out/"probe_harness.sv")}\n'
    script += 'prep -top ConstantProbe -flatten\n' + formal_lower_command(args.yosys) + 'check -assert\n'
    script += f'tee -o {yosys_path(out/"domain_nonempty.log")} sat -set-assumes -show instruction_i\n'
    for i, node in enumerate(nodes):
        for value in (0, 1):
            script += f'tee -o {yosys_path(out/f"constant_{i:04d}_{value}.log")} sat -set-assumes -prove probe_{i:04d} {value}\n'
    record = {'status': 'running', 'scope': 'Exhaustive combinational scalar-controllability baseline, not strongest program-only sequential Pscorr',
        'domain': args.domain, 'domain_expression': expression, 'scalar_nodes': len(nodes),
        'attempted_constants': len(candidates), 'prepared_manifest_sha256': digest(prepared/'manifest.json'),
        'source_hashes': {str(path): digest(path) for path in [Path(__file__), REPO/'odc/state_candidates.py', REPO/'odc/temporal.py']},
        'capacity_parameters': manifest['capacity_parameters'], 'accepted': [], 'no_timing_assumptions': True,
        'full_core_equivalence_status': 'Requires original decoder-input domain; domain propagation not yet certified'}
    def save():
        (out/'summary.json').write_text(json.dumps(record, indent=2)+'\n')
    save()
    try:
        record['constant_search'] = checked_yosys(args.yosys, script, out, 'constant_search', args.timeout)
        assert (out/'domain_nonempty.log').read_text().count('SAT solving finished - model found:') == 1
        current = design
        for i, node in enumerate(nodes):
            proven = []
            for value in (0, 1):
                log = (out/f'constant_{i:04d}_{value}.log').read_text()
                assert 'ERROR:' not in log and 'timeout' not in log.lower()
                success = log.count('SAT proof finished - no model found: SUCCESS!')
                failure = log.count('SAT proof finished - model found: FAIL!')
                assert success + failure == 1, f'Unknown SAT status for node {i}/{value}'
                if success:
                    proven.append(value)
            assert len(proven) <= 1, 'Nonempty domain cannot prove both constants'
            if proven:
                candidate = {**node, 'constant': proven[0]}
                current = replace_scalar_constant(current, 'DecoderBase', candidate)
                record['accepted'].append(candidate)
        reference, candidate_v = out/'reference.v', out/'candidate.v'
        export_design(design, 'DecoderBase', 'DecoderBase', reference, args.yosys, args.timeout)
        export_design(current, 'DecoderBase', 'DecoderCandidate', candidate_v, args.yosys, args.timeout)
        harness = out/'harness.sv'
        harness.write_bytes((prepared/(args.domain+'.sv')).read_bytes())
        assert digest(harness) == manifest['domains'][args.domain]['harness_sha256']
        record['combined_all_output_proof'] = prove_pair(reference, candidate_v, harness, 'TemporalMiter', out/'combined_proof',
            yosys=args.yosys, smtbmc=str(Path(args.yosys).with_name('yosys-smtbmc')), solver='z3', depth=2,
            timeout=60, engine='pdr', abc=args.abc, assert_state_correspondence=False)
        if not record['combined_all_output_proof']['proven']:
            raise ValueError('Combined original/candidate decoder equivalence did not prove')
        whole = json.loads((prepared/'whole_core.json').read_text())
        for candidate in record['accepted']:
            name = candidate['cell']
            assert whole['modules']['datapath']['cells'][name] == design['modules']['DecoderBase']['cells'][name]
            whole['modules']['datapath']['cells'][name] = copy.deepcopy(current['modules']['DecoderBase']['cells'][name])
        (out/'candidate_whole_core.json').write_text(json.dumps(whole)+'\n')
        checked_yosys(args.yosys, f'read_json {yosys_path(out/"candidate_whole_core.json")}\ncheck -assert\n'
            'select -assert-none t:$assume t:$assert t:$cover t:$check\nselect *\nopt -full\ncheck -assert\n'
            f'write_rtlil {yosys_path(out/"candidate_whole_core.il")}\n'
            f'tee -o {yosys_path(out/"candidate_native_stat.json")} stat -json\n', out, 'native_cleanup', 60)
        record['candidate_whole_core_sha256'] = digest(out/'candidate_whole_core.json')
        record['candidate_native_il_sha256'] = digest(out/'candidate_whole_core.il')
        record['status'] = 'decoder_equivalence_proved_native_candidate_emitted'
    except (AssertionError, RuntimeError, ValueError, OSError, KeyError) as error:
        record['status'] = 'failed'; record['error'] = str(error)
    for name, sha in record['source_hashes'].items():
        if digest(Path(name)) != sha:
            record.update(status='failed', error='Implementation changed during run: '+name)
    save()
    print(json.dumps({'status': record['status'], 'accepted_constants': len(record['accepted']), 'summary': str(out/'summary.json')}))
    return 0 if record['status'] == 'decoder_equivalence_proved_native_candidate_emitted' else 1


if __name__ == '__main__':
    raise SystemExit(main())
