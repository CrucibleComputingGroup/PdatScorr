"""Native state helpers add obligations; state factoring must prove transitions."""
import copy
import importlib.util
import json
from pathlib import Path
import shutil
import sys

import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
HELPERS = ROOT / 'experiments/bounded_dynamic/len5/phase_sharing'


def load_helper(name):
    spec = importlib.util.spec_from_file_location('phase_' + name, HELPERS / (name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


native = load_helper('proof')
factor = load_helper('factor_state')
last_writer = load_helper('last_writer')
from odc.temporal import checked_yosys, formal_lower_command, proof_passed, run_command
from odc.temporal import export_design
from odc.bank_sharing import bank_candidates, merge_banks

MODERN = ROOT.parents[2] / 'tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys'
YOSYS = str(MODERN) if MODERN.is_file() else shutil.which('yosys')
SMTBMC = str(Path(YOSYS).with_name('yosys-smtbmc')) if YOSYS else None
integration = pytest.mark.skipif(not YOSYS or not shutil.which('z3'), reason='Yosys/Z3 required')


def matching_fixture():
    cells = {}
    for name, bits in [('reference', [10, 11, 12]), ('candidate', [20, 21, 22])]:
        cells[name] = {'type': '$adff', 'parameters': {'WIDTH': 3, 'CLK_POLARITY': 1,
                            'ARST_POLARITY': 0, 'ARST_VALUE': '000'},
                      'connections': {'CLK': [2], 'ARST': [3], 'D': [4, 5, 6], 'Q': bits},
                      'port_directions': {'CLK': 'input', 'ARST': 'input', 'D': 'input', 'Q': 'output'}}
    return {'modules': {'Miter': {'cells': cells,
        'ports': {'clk': {'direction': 'input', 'bits': [2]}},
        'netnames': {'reference.q': {'bits': [10, 11, 12]},
                     'candidate.q': {'bits': [20, 21, 22]},
                     'reference.q_alias': {'bits': [10]}, 'candidate.q_alias': {'bits': [20]},
                     'reference.d': {'bits': [4, 5, 6]}, 'candidate.d': {'bits': [4, 5, 6]}}}}}


def test_native_matches_are_deduplicated_assertions_not_assumptions():
    design = matching_fixture()
    old = copy.deepcopy(design['modules']['Miter'])
    result = native.assert_native_correspondence(design, 'Miter')
    assert result['pairs'] == [(10, 20), (11, 21), (12, 22)]
    assert result['assumptions_added'] == 0 and result['initial_pairing'] is False
    module = design['modules']['Miter']
    assert module['ports'] == old['ports'] and module['netnames'] == old['netnames']
    for name, cell in old['cells'].items():
        assert module['cells'][name] == cell
    added = [cell for name, cell in module['cells'].items() if name not in old['cells']]
    assert {cell['type'] for cell in added} == {'$eq', '$assert'}
    assert next(cell for cell in added if cell['type'] == '$assert')['connections']['EN'] == ['1']


@pytest.mark.parametrize('reference_alias,candidate_alias', [(10, 21), (11, 20)])
def test_every_edge_in_many_to_one_or_one_to_many_aliases_is_excluded(reference_alias, candidate_alias):
    design = matching_fixture()
    nets = design['modules']['Miter']['netnames']
    nets['reference.merged'] = {'bits': [reference_alias]}
    nets['candidate.merged'] = {'bits': [candidate_alias]}
    result = native.assert_native_correspondence(design, 'Miter')
    assert result['pairs'] == [(12, 22)]
    assert result['excluded_edge_count'] == 3


def test_native_certificate_cannot_be_applied_twice():
    design = matching_fixture()
    native.assert_native_correspondence(design, 'Miter')
    with pytest.raises(ValueError, match='already present'):
        native.assert_native_correspondence(design, 'Miter')


def prepare_toy(tmp_path, *, wrong_next=False, low_enable=False):
    source = tmp_path / 'source.sv'
    expression = 'd ^ 4\'h1' if wrong_next else 'd'
    enable = '!en' if low_enable else 'en'
    source.write_text(f'''module Ref(input clk,rst_ni,en,input [3:0] d,output reg [3:0] q);
      always @(posedge clk or negedge rst_ni)
        if (!rst_ni) q<=4'h5; else if ({enable}) q<=d;
    endmodule
    module Cand(input clk,rst_ni,en,input [3:0] d,output reg [3:0] q);
      always @(posedge clk or negedge rst_ni)
        if (!rst_ni) q<=4'h5; else if ({enable}) q<={expression};
    endmodule
    module Miter(input clk,rst_ni,en,input [3:0] d);
      wire [3:0] a,b;
      Ref reference(clk,rst_ni,en,d,a);
      Cand candidate(clk,rst_ni,en,d,b);
      always @* begin
        if ($initstate) assume(!rst_ni);
        assert(a==b);
      end
    endmodule''')
    output = tmp_path / 'native.json'
    checked_yosys(YOSYS, f'read_verilog -formal -sv "{source}"\n'
        'hierarchy -top Miter\nproc\nflatten\nopt_dff\nopt_clean\ncheck -assert\n'
        + formal_lower_command(YOSYS) + f'write_json "{output}"\n', tmp_path, 'prepare', 20)
    return json.loads(output.read_text())


def prove_json(tmp_path, design):
    source, smt = tmp_path / 'factored.json', tmp_path / 'model.smt2'
    source.write_text(json.dumps(design))
    checked_yosys(YOSYS, f'read_json "{source}"\ncheck -assert\nasync2sync\ndffunmap\n'
                   f'write_smt2 -wires "{smt}"\n', tmp_path, 'export', 20)
    command = [SMTBMC, '-s', 'z3', '-t', '4', '--noprogress']
    base = run_command(command + [str(smt)], tmp_path / 'base.log', 20)
    step = run_command(command + ['-i', str(smt)], tmp_path / 'step.log', 20)
    return proof_passed(base) and proof_passed(step), base, step


@integration
@pytest.mark.parametrize('wrong_next,low_enable', [(False, False), (False, True), (True, False)])
def test_factored_real_transitions_prove_identity_and_reject_wrong_next(tmp_path, wrong_next, low_enable):
    design = prepare_toy(tmp_path, wrong_next=wrong_next, low_enable=low_enable)
    before = copy.deepcopy(design['modules']['Miter'])
    matches = native.assert_native_correspondence(design, 'Miter')
    assert matches['asserted_state_pairs'] == 4
    result = factor.factor_common_state(design, 'Miter', matches['pairs'])
    module = design['modules']['Miter']
    assert result['factored_state_bits'] == 4 and result['assumptions_added'] == 0
    assert result['fresh_state_inputs'] == 0
    assumptions = lambda m: {name: cell for name, cell in m['cells'].items() if cell['type'] == '$assume'}
    assert assumptions(module) == assumptions(before)
    assert module['ports'] == before['ports']
    old_q = sum(len(cell['connections']['Q']) for cell in before['cells'].values() if cell['type'] in ('$adff', '$adffe'))
    new_q = sum(len(cell['connections']['Q']) for cell in module['cells'].values() if cell['type'] in ('$adff', '$adffe'))
    assert old_q - new_q == 4
    proven, base, step = prove_json(tmp_path, design)
    assert proven is (not wrong_next), (base, step)
    if wrong_next:
        # The functional output comparison is now tautological. Only the
        # original next-state obligation can detect this bad transformation.
        assert 'Status: FAILED' in Path(base['log']).read_text()


@integration
def test_factoring_rejects_unconstrained_reset_values(tmp_path):
    design = prepare_toy(tmp_path)
    matches = native.assert_native_correspondence(design, 'Miter')
    for cell in design['modules']['Miter']['cells'].values():
        if cell['type'] in ('$adff', '$adffe'):
            cell['parameters']['ARST_VALUE'] = 'xxxx'
    with pytest.raises(ValueError, match='[Rr]eset|[Bb]inary|[Cc]onstant'):
        factor.factor_common_state(design, 'Miter', matches['pairs'])


@integration
def test_factoring_rejects_missing_initial_reset_assumption(tmp_path):
    design = prepare_toy(tmp_path)
    matches = native.assert_native_correspondence(design, 'Miter')
    module = design['modules']['Miter']
    module['cells'] = {name: cell for name, cell in module['cells'].items() if cell['type'] != '$assume'}
    with pytest.raises(ValueError, match='initial-reset assumption'):
        factor.factor_common_state(design, 'Miter', matches['pairs'])


@integration
def test_factoring_checks_original_enable_polarity_before_sharing_q(tmp_path):
    design = prepare_toy(tmp_path)
    matches = native.assert_native_correspondence(design, 'Miter')
    candidate_q = {c for r, c in matches['pairs']}
    for cell in design['modules']['Miter']['cells'].values():
        if cell['type'] == '$adffe' and candidate_q.intersection(cell['connections']['Q']):
            assert int(cell['parameters']['EN_POLARITY'], 2) == 1
            cell['parameters']['EN_POLARITY'] = '0'
    factor.factor_common_state(design, 'Miter', matches['pairs'])
    proven, base, step = prove_json(tmp_path, design)
    assert not proven and 'Status: FAILED' in Path(base['log']).read_text(), (base, step)


@integration
def test_partial_bank_factoring_preserves_unpaired_ff_bits_and_reset_values(tmp_path):
    design = prepare_toy(tmp_path)
    matches = native.assert_native_correspondence(design, 'Miter')
    selected = matches['pairs'][::2]
    reference_q = {r for r, c in matches['pairs']}
    remaining_candidate_q = {c for r, c in matches['pairs'] if (r, c) not in selected}
    factor.factor_common_state(design, 'Miter', selected)
    cells = design['modules']['Miter']['cells'].values()
    qbits = {q for cell in cells if cell['type'] in ('$adff', '$adffe') for q in cell['connections']['Q']}
    assert qbits == reference_q | remaining_candidate_q
    proven, base, step = prove_json(tmp_path, design)
    assert proven, (base, step)


def prepare_bank_pair(tmp_path, *, overlapping=False, wrong_priority=False):
    source, original_json = tmp_path / 'banks.sv', tmp_path / 'banks.json'
    output = '{a,b}' if overlapping else '(selected ? b : a)'
    width = 8 if overlapping else 4
    source.write_text(f'''module Bank(input clk,rst_ni,select,input [3:0] da,db,
                                     output [{width-1}:0] q, output reg [2:0] history);
      reg [3:0] a,b;
      reg selected;
      always @(posedge clk or negedge rst_ni) begin
        if (!rst_ni) begin a<=4'h5; b<=4'h5; selected<=0; history<=0; end
        else begin
          if (!select) a<=da;
          if (select) b<=db;
          selected<=select;
          history<=history+1;
        end
      end
      assign q={output};
    endmodule''')
    checked_yosys(YOSYS, f'read_verilog -sv "{source}"\nhierarchy -top Bank\nproc\nopt\n'
        f'write_json "{original_json}"\n', tmp_path, 'bank_source', 20)
    original = json.loads(original_json.read_text())
    candidates = bank_candidates(original, 'Bank', min_width=4)
    assert len(candidates) == 1
    candidate = candidates[0]
    changed = merge_banks(original, 'Bank', candidate, wrong_priority=wrong_priority)
    original_v, changed_v = tmp_path / 'original.v', tmp_path / 'changed.v'
    export_design(original, 'Bank', 'Bank', original_v, YOSYS, 20)
    export_design(changed, 'Bank', 'BankCandidate', changed_v, YOSYS, 20)
    harness = tmp_path / 'harness.sv'
    harness.write_text(f'''module Miter(input clk,rst_ni,select,input [3:0] da,db);
      wire [{width-1}:0] a,b;
      wire [2:0] ah,bh;
      Bank reference(clk,rst_ni,select,da,db,a,ah);
      BankCandidate candidate(clk,rst_ni,select,da,db,b,bh);
      always @* begin
        if ($initstate) assume(!rst_ni);
        assert(a==b);
        assert(ah==bh);
      end
    endmodule''')
    native_json = tmp_path / 'native.json'
    checked_yosys(YOSYS, f'read_verilog -formal -sv "{original_v}" "{changed_v}" "{harness}"\n'
        'hierarchy -top Miter\nproc\nflatten\nopt_dff\nopt_clean\ncheck -assert\n'
        + formal_lower_command(YOSYS) + f'write_json "{native_json}"\n', tmp_path, 'prepare', 20)
    return json.loads(native_json.read_text()), original, candidate


@integration
@pytest.mark.parametrize('overlapping,wrong_priority,expected',
                         [(False, False, True), (False, True, False), (True, False, False)])
def test_factoring_and_last_writer_cannot_hide_wrong_shared_bank_or_live_values(
        tmp_path, overlapping, wrong_priority, expected):
    design, original, bank = prepare_bank_pair(tmp_path, overlapping=overlapping,
                                               wrong_priority=wrong_priority)
    before = copy.deepcopy(design['modules']['Miter'])
    matches = native.assert_native_correspondence(design, 'Miter')
    # All four bits of each original bank map to the same four candidate bits.
    # They must remain ambiguous and not become equality assumptions/factors.
    assert matches['excluded_edge_count'] == 8
    assert matches['asserted_state_pairs'] == 3  # unchanged history counter
    monitor = last_writer.add_last_writer_assertion(design, 'Miter', original, 'Bank', bank)
    assert monitor['assumptions_added'] == 0 and monitor['width'] == 4
    result = factor.factor_common_state(design, 'Miter', matches['pairs'])
    assert result['factored_state_bits'] == 3
    module = design['modules']['Miter']
    assumptions = lambda m: {n: c for n, c in m['cells'].items() if c['type'] == '$assume'}
    assert assumptions(module) == assumptions(before)
    assert module['ports'] == before['ports']
    proven, base, step = prove_json(tmp_path, design)
    assert proven is expected, (base, step)
    if not expected:
        assert 'Status: FAILED' in Path(base['log']).read_text()
