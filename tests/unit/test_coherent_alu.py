"""Coherent function abstraction may share only equal complete input tuples."""
import copy
import importlib.util
import json
from pathlib import Path
import shutil
import sys

import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
HELPER = ROOT / 'experiments/bounded_dynamic/len5/phase_sharing/coherent_alu.py'
spec = importlib.util.spec_from_file_location('phase_coherent_alu', HELPER)
coherent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(coherent)
from odc.temporal import checked_yosys, proof_passed, run_command

MODERN = ROOT.parents[2] / 'tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys'
YOSYS = str(MODERN) if MODERN.is_file() else shutil.which('yosys')
SMTBMC = str(Path(YOSYS).with_name('yosys-smtbmc')) if YOSYS else None
pytestmark = pytest.mark.skipif(not YOSYS or not shutil.which('z3'), reason='Yosys/Z3 required')


def fixture(*, changed_input=None, different_function=False, undefined_result=False):
    cells, nets = {}, {}
    def cell(name, kind, con, params=None, outputs=('Y',)):
        cells[name] = {'hide_name': 0, 'type': kind, 'parameters': params or {}, 'attributes': {},
                       'connections': con,
                       'port_directions': {port: 'output' if port in outputs else 'input' for port in con}}
    binary = {'A_SIGNED': 0, 'B_SIGNED': 0, 'A_WIDTH': 4, 'B_WIDTH': 4, 'Y_WIDTH': 4}
    ports = {'clk': {'direction': 'input', 'bits': [2]}, 'rst_ni': {'direction': 'input', 'bits': [3]},
             'ctl': {'direction': 'input', 'bits': [4, 5]},
             'x': {'direction': 'input', 'bits': [6, 7, 8, 9]},
             'y': {'direction': 'input', 'bits': [10, 11, 12, 13]}}
    for instance, offset in [('reference', 20), ('candidate', 60)]:
        inputs = {'ctl_i': [4, 5], 'rs1_i': [6, 7, 8, 9], 'rs2_i': [10, 11, 12, 13]}
        if instance == 'candidate' and changed_input:
            role = changed_input
            original = inputs[role]
            replacement = list(range(100, 100 + len(original)))
            width = len(original)
            cell('changed_' + role, '$xor', {'A': original, 'B': ['1'] + ['0']*(width-1), 'Y': replacement},
                 {**binary, 'A_WIDTH': width, 'B_WIDTH': width, 'Y_WIDTH': width})
            inputs[role] = replacement
        prefix = instance + '.u_alu.u_alu.'
        for role, bits in inputs.items():
            nets[prefix + role] = {'hide_name': 0, 'attributes': {}, 'bits': bits}
        summed, xorred, result, registered = [list(range(offset+i, offset+i+4)) for i in (0, 4, 8, 12)]
        cell(prefix+'add', '$sub' if different_function and instance == 'candidate' else '$add',
             {'A': inputs['rs1_i'], 'B': inputs['rs2_i'], 'Y': summed}, dict(binary))
        cell(prefix+'xor', '$xor', {'A': inputs['rs1_i'], 'B': inputs['rs2_i'], 'Y': xorred}, dict(binary))
        cell(prefix+'select_result', '$mux', {'A': ['x']*4 if undefined_result else summed,
             'B': xorred, 'S': [inputs['ctl_i'][0]], 'Y': result}, {'WIDTH': 4})
        nets[prefix+'result'] = {'hide_name': 0, 'attributes': {}, 'bits': result}
        cell(instance+'.history', '$adff', {'CLK': [2], 'ARST': [3], 'D': result, 'Q': registered},
             {'WIDTH': 4, 'CLK_POLARITY': 1, 'ARST_POLARITY': 0, 'ARST_VALUE': '0000'}, outputs=('Q',))
    cell('outputs_equal', '$eq', {'A': [32, 33, 34, 35], 'B': [72, 73, 74, 75], 'Y': [120]},
         {**binary, 'Y_WIDTH': 1})
    cell('output_assert', '$assert', {'A': [120], 'EN': ['1']}, outputs=())
    cell('reset_low', '$logic_not', {'A': [3], 'Y': [121]}, {'A_SIGNED': 0, 'A_WIDTH': 1, 'Y_WIDTH': 1})
    cell('initial', '$initstate', {'Y': [122]})
    cell('reset_assume', '$assume', {'A': [121], 'EN': [122]}, outputs=())
    return {'modules': {'Miter': {'attributes': {'top': '1'}, 'cells': cells, 'ports': ports, 'netnames': nets}}}


def prove(tmp_path, design):
    source, smt = tmp_path/'proof.json', tmp_path/'proof.smt2'
    source.write_text(json.dumps(design))
    checked_yosys(YOSYS, f'read_json "{source}"\nhierarchy -top Miter\ncheck -assert\n'
                  f'async2sync\ndffunmap\nwrite_smt2 -wires "{smt}"\n', tmp_path, 'export', 20)
    command = [SMTBMC, '-s', 'z3', '-t', '4', '--noprogress']
    base = run_command(command + [str(smt)], tmp_path/'base.log', 20)
    step = run_command(command + ['-i', str(smt)], tmp_path/'step.log', 20)
    return proof_passed(base) and proof_passed(step), base, step


def test_equal_complete_tuples_share_symbolic_result_without_changing_ff_state_or_assumptions(tmp_path):
    design = fixture()
    old = copy.deepcopy(design['modules']['Miter'])
    result = coherent.abstract_alu(design, 'Miter', tmp_path, yosys=YOSYS)
    module = design['modules']['Miter']
    assert result['assumptions_added'] == 0 and result['full_input_tuple_bits'] == 10
    assert module['ports'] == old['ports'] and module['netnames'] == old['netnames']
    assert module['cells']['reset_assume'] == old['cells']['reset_assume']
    for side in ('reference', 'candidate'):
        before, after = old['cells'][side+'.history'], module['cells'][side+'.history']
        assert after['type'] == before['type'] and after['parameters'] == before['parameters']
        for port in ('Q', 'CLK', 'ARST'):
            assert after['connections'][port] == before['connections'][port]
        assert after['connections']['D'] != before['connections']['D']
        for kind in ('add', 'xor', 'select_result'):
            name = side+'.u_alu.u_alu.'+kind
            assert module['cells'][name] == old['cells'][name]
    prefix = '$pscorr_coherent_alu_'
    equal = module['cells'][prefix+'inputs_equal']['connections']
    assert equal['A'] == equal['B'] == [4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
    mux = module['cells'][prefix+'conditional_coherence']['connections']
    assert mux['A'] == module['cells'][prefix+'b']['connections']['Y']
    assert mux['B'] == module['cells'][prefix+'a']['connections']['Y']
    assert set(mux['A']).isdisjoint(mux['B'])
    assert sum(cell['type'] == '$anyseq' for cell in module['cells'].values()) == 2
    proven, base, step = prove(tmp_path, design)
    assert proven, (base, step)


@pytest.mark.parametrize('changed_input', ['ctl_i', 'rs1_i', 'rs2_i'])
def test_wrong_operation_or_operand_keeps_independent_results_and_fails(tmp_path, changed_input):
    design = fixture(changed_input=changed_input)
    before = copy.deepcopy(design['modules']['Miter'])
    coherent.abstract_alu(design, 'Miter', tmp_path, yosys=YOSYS)
    module = design['modules']['Miter']
    assert module['cells']['reset_assume'] == before['cells']['reset_assume']
    assert module['cells']['changed_'+changed_input] == before['cells']['changed_'+changed_input]
    proven, base, step = prove(tmp_path, design)
    assert not proven and 'Status: FAILED' in Path(base['log']).read_text(), (base, step)


def test_different_native_function_is_rejected_without_mutation(tmp_path):
    design = fixture(different_function=True)
    before = copy.deepcopy(design)
    with pytest.raises(ValueError, match='cones differ'):
        coherent.abstract_alu(design, 'Miter', tmp_path, yosys=YOSYS)
    assert design == before


def test_observable_undefined_result_is_rejected_without_mutation(tmp_path):
    design = fixture(undefined_result=True)
    before = copy.deepcopy(design)
    with pytest.raises(ValueError, match='undefined|definedness'):
        coherent.abstract_alu(design, 'Miter', tmp_path, yosys=YOSYS)
    assert design == before
    assert 'SAT solving finished - model found' in (tmp_path/'alu_definedness.log').read_text()


def test_different_unused_role_width_cannot_misalign_tuple_equality(tmp_path):
    design = fixture()
    module = design['modules']['Miter']
    # ctl[1] is unused by the function. Removing it preserves the output
    # signature but shifts operand positions in a concatenated tuple.
    module['netnames']['candidate.u_alu.u_alu.ctl_i']['bits'] = [4]
    a = coherent.signature(module, 'reference.u_alu.u_alu.')
    b = coherent.signature(module, 'candidate.u_alu.u_alu.')
    assert a['output_signature'] == b['output_signature']
    before = copy.deepcopy(design)
    with pytest.raises(ValueError, match='width|tuple|interface'):
        coherent.abstract_alu(design, 'Miter', tmp_path, yosys=YOSYS)
    assert design == before
