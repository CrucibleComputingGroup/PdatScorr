"""Generic temporal ODC integration tests on tiny sequential circuits.

These tests elaborate unit fixtures and run SMT induction or PDR; they do not run
processor experiments. All stimuli and original state drivers remain intact.
"""
import copy
import json
from pathlib import Path
import shutil
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from odc.temporal import (digest, equality_candidates, export_design,
                          narrow_equality, proof_passed, prove_pair)
import odc.temporal as temporal

TOOLS = {name: shutil.which(name) for name in ('yosys', 'yosys-smtbmc', 'z3')}
pytestmark = pytest.mark.skipif(not all(TOOLS.values()), reason='Yosys, smtbmc and Z3 required')

CONDITIONAL = '''
module Toy(input clk, rst, valid_i, input [3:0] tag, probe, output hit);
  reg valid_q = 0;
  reg [3:0] tag_q = 0;
  always @(posedge clk) begin
    if (rst) begin valid_q <= 0; tag_q <= 0; end
    else begin valid_q <= valid_i; tag_q <= tag; end
  end
  assign hit = valid_q && (tag_q == probe);
endmodule
'''


def run(argv, cwd):
    result = subprocess.run(argv, cwd=cwd, text=True, capture_output=True, timeout=40)
    assert result.returncode == 0, result.stdout + result.stderr
    return result


def elaborate(tmp_path, source, top='Toy'):
    rtl, design = tmp_path/'toy.sv', tmp_path/'toy.json'
    rtl.write_text(source)
    run([TOOLS['yosys'], '-Q', '-T', '-p',
         f'read_verilog -sv "{rtl}"; hierarchy -top {top}; proc; opt; write_json "{design}"'], tmp_path)
    return design


def harness(tmp_path, constrain_tag=True):
    text = '''
module TemporalMiter(input clk);
  (* anyseq *) reg rst, valid_i;
  (* anyseq *) reg [3:0] tag, probe;
  wire original_hit, candidate_hit;
  Toy reference(clk, rst, valid_i, tag, probe, original_hit);
  ToyCandidate candidate(clk, rst, valid_i, tag, probe, candidate_hit);
  reg initial_cycle = 1;
  always @(posedge clk) initial_cycle <= 0;
  always @* begin
    if (initial_cycle) assume(rst);
    assume(probe[3:2] == 0);
    TAG_CONTRACT
    assert(original_hit == candidate_hit);
  end
endmodule
'''.replace('TAG_CONTRACT', 'if (!rst && valid_i) assume(tag[3:2] == 0);' if constrain_tag else '')
    path = tmp_path/'harness.sv'
    path.write_text(text)
    return path


def proof(reference, candidate, monitor, directory, depth=4, **kwargs):
    return prove_pair(reference, candidate, monitor, 'TemporalMiter', directory,
                      yosys=TOOLS['yosys'], smtbmc=TOOLS['yosys-smtbmc'],
                      solver='z3', depth=depth, timeout=20, **kwargs)


def export_pair(tmp_path, design, candidate):
    reference, modified = tmp_path/'reference.v', tmp_path/'candidate.v'
    export_design(design, 'Toy', 'Toy', reference, TOOLS['yosys'], 20)
    export_design(narrow_equality(design, 'Toy', candidate), 'Toy', 'ToyCandidate',
                  modified, TOOLS['yosys'], 20)
    return reference, modified


def test_end_to_end_conditional_odc_and_untouched_drivers(tmp_path):
    source = elaborate(tmp_path, CONDITIONAL)
    original = json.loads(source.read_text())
    monitor = harness(tmp_path)
    source_hash, monitor_hash = digest(source), digest(monitor)
    out = tmp_path/'discovery'
    run([sys.executable, str(ROOT/'scripts/analyze_temporal_odc.py'), str(source),
         '--top', 'Toy', '--candidate-top', 'ToyCandidate', '--harness', str(monitor),
         '--output', str(out), '--yosys', TOOLS['yosys'], '--smtbmc', TOOLS['yosys-smtbmc'],
         '--depth', '4', '--timeout', '20'], tmp_path)
    report = json.loads((out/'report.json').read_text())
    assert report['status'] == 'proved'
    assert report['identity_proof']['proven'] and report['combined_proof']['proven']
    assert len(report['accepted']) == 1
    assert report['accepted'][0]['retained_low_bits'] == 2
    assert any(not p['proof']['proven'] for p in report['probes'])
    assert report['combined_proof']['reference_sha256'] == digest(out/'reference.v')
    assert report['combined_proof']['candidate_sha256'] == digest(out/'optimized.v')
    assert digest(source) == source_hash and digest(monitor) == monitor_hash
    changed = json.loads((out/'optimized.json').read_text())['modules']['Toy']
    before = original['modules']['Toy']
    assert changed['ports'] == before['ports']
    assert changed['netnames'] == before['netnames']
    modified_cells = [name for name in before['cells'] if before['cells'][name] != changed['cells'][name]]
    assert modified_cells == [report['accepted'][0]['cell']]
    for name, cell in before['cells'].items():
        if cell['type'] != '$eq':
            assert changed['cells'][name] == cell  # Includes every FF/reset/update driver.


def test_same_mutation_rejected_without_contract(tmp_path):
    design = json.loads(elaborate(tmp_path, CONDITIONAL).read_text())
    candidate = next(c for c in equality_candidates(design, 'Toy') if c['retained_low_bits'] == 2)
    before = copy.deepcopy(design)
    reference, modified = export_pair(tmp_path, design, candidate)
    result = proof(reference, modified, harness(tmp_path, constrain_tag=False), tmp_path/'negative')
    assert not result['proven'] and not proof_passed(result['base'])
    assert design == before


def test_bounded_pass_cannot_authorize(tmp_path):
    source = '''
module Toy(input clk, output hit);
  reg [3:0] age = 0;
  always @(posedge clk) age <= age + 1;
  assign hit = (age == 4'd11);
endmodule
'''
    design = json.loads(elaborate(tmp_path, source).read_text())
    candidate = next(c for c in equality_candidates(design, 'Toy') if c['retained_low_bits'] == 2)
    reference, modified = export_pair(tmp_path, design, candidate)
    monitor = tmp_path/'harness.sv'
    monitor.write_text('''
module TemporalMiter(input clk);
  wire a,b;
  Toy reference(clk,a);
  ToyCandidate candidate(clk,b);
  always @* assert(a == b);
endmodule
''')
    result = proof(reference, modified, monitor, tmp_path/'bounded', depth=2)
    assert proof_passed(result['base']), result
    assert not proof_passed(result['induction']) and not result['proven']


def state_pair(tmp_path, reference_init='', candidate_init=''):
    template = '''module TOP(input clk, input [3:0] d, output reg [3:0] q INIT);
  always @(posedge clk) q <= d;
endmodule
'''
    reference, candidate = tmp_path/'reference.v', tmp_path/'candidate.v'
    reference.write_text(template.replace('TOP','Toy').replace('INIT',reference_init))
    candidate.write_text(template.replace('TOP','ToyCandidate').replace('INIT',candidate_init))
    monitor = tmp_path/'harness.sv'
    monitor.write_text('''module TemporalMiter(input clk);
  (* anyseq *) reg [3:0] d;
  wire [3:0] a,b;
  Toy reference(clk,d,a);
  ToyCandidate candidate(clk,d,b);
  always @* assert(a == b);
endmodule
''')
    return reference, candidate, monitor


def test_same_arbitrary_initial_state_is_paired_only_initially(tmp_path):
    result = proof(*state_pair(tmp_path), tmp_path/'arbitrary')
    assert result['proven'], result
    assert len(result['clock_model']['clocks']) == 1
    assert result['clock_model']['clocks'][0][1] == 1
    assert result['initial_state']['paired_state_bits'] == 4
    miter = json.loads((tmp_path/'arbitrary/miter.json').read_text())['modules']['TemporalMiter']
    enables = [c for c in miter['cells'].values() if c['type'] == '$initstate']
    assert len(enables) == 1
    assume = next(c for n,c in miter['cells'].items() if n.startswith('$pscorr_initial_state_') and c['type']=='$assume')
    assert assume['connections']['EN'] == enables[0]['connections']['Y']
    invariant = next(c for n,c in miter['cells'].items() if n.startswith('$pscorr_initial_state_') and c['type']=='$assert')
    assert invariant['connections']['EN'] == ['1']


@pytest.mark.parametrize('engine', ['induction', 'pdr'])
@pytest.mark.parametrize('body', [
    'always @(posedge clk) q[0] <= d[0]; always @(posedge clk_b) q[1] <= d[1];',
    'always @(posedge clk) q[0] <= d[0]; always @(negedge clk) q[1] <= d[1];',
    'wire gated_clk = clk & en; always @(posedge gated_clk) q <= d;',
], ids=['independent_clocks', 'opposite_edges', 'gated_clock'])
def test_unsupported_clock_identity_is_rejected_before_solver(tmp_path, engine, body):
    template = '''module TOP(input clk, clk_b, en, input [1:0] d, output reg [1:0] q);
      BODY
    endmodule'''.replace('BODY', body)
    reference, candidate, monitor = tmp_path/'reference.v', tmp_path/'candidate.v', tmp_path/'harness.sv'
    reference.write_text(template.replace('TOP', 'Toy'))
    candidate.write_text(template.replace('TOP', 'ToyCandidate'))
    monitor.write_text('''module TemporalMiter(input clk, clk_b);
      (* anyseq *) reg en;
      (* anyseq *) reg [1:0] d;
      wire [1:0] a,b;
      Toy reference(clk,clk_b,en,d,a);
      ToyCandidate candidate(clk,clk_b,en,d,b);
      always @* assert(a == b);
    endmodule''')
    result = proof(reference, candidate, monitor, tmp_path/'unsupported_clock',
                   engine=engine, abc='must-not-run-abc')
    assert not result['proven'] and 'shared scalar top-level input' in result['error'], result
    assert 'base' not in result and 'pdr' not in result
    assert 'aig_export' not in result and 'smt_export' not in result


def test_async_reset_normalizes_to_checked_single_clock(tmp_path):
    template = '''module TOP(input clk,rst,d, output reg q);
      always @(posedge clk or posedge rst) if (rst) q <= 0; else q <= d;
    endmodule'''
    reference, candidate, monitor = tmp_path/'reference.v', tmp_path/'candidate.v', tmp_path/'harness.sv'
    reference.write_text(template.replace('TOP', 'Toy'))
    candidate.write_text(template.replace('TOP', 'ToyCandidate'))
    monitor.write_text('''module TemporalMiter(input clk);
      (* anyseq *) reg rst,d;
      wire a,b;
      Toy reference(clk,rst,d,a);
      ToyCandidate candidate(clk,rst,d,b);
      reg initial_cycle = 1;
      always @(posedge clk) initial_cycle <= 0;
      always @* begin
        if (initial_cycle) assume(rst);
        assert(a == b);
      end
    endmodule''')
    result = proof(reference, candidate, monitor, tmp_path/'async_normalized')
    assert result['proven'], result
    assert len(result['clock_model']['clocks']) == 1
    cells = json.loads((tmp_path/'async_normalized/miter.json').read_text())['modules']['TemporalMiter']['cells']
    assert any(c['type'] == '$dff' for c in cells.values())
    assert not any(c['type'] in {'$adff', '$adffe', '$sdff', '$dffe'} for c in cells.values())


@pytest.mark.parametrize('cell_type', ['$adff', '$aldff', '$dffe', '$sdffe', '$dffsr',
                                      '$dlatchsr', '$_DFF_P_', '$_DLATCH_P_', '$mem_v2'])
def test_remaining_sequential_cell_types_fail_clock_validation(cell_type):
    design = {'modules': {'Toy': {'ports': {'clk': {'direction': 'input', 'bits': [2]}},
        'cells': {'unhandled_state': {'type': cell_type, 'connections': {}, 'parameters': {}}}}}}
    with pytest.raises(ValueError, match='Residual sequential cells'):
        temporal.validate_single_clock(design, 'Toy')


def test_explicit_initial_state_difference_is_not_assumed_away(tmp_path):
    result = proof(*state_pair(tmp_path, "= 4'd0", "= 4'd1"), tmp_path/'initial_negative')
    assert not result['proven'], 'Initial-state equality must not make conflicting initializations vacuous'


def test_optional_state_helper_keeps_initial_pairing_and_functional_observations(tmp_path):
    reference, candidate, monitor = state_pair(tmp_path)
    result = proof(reference, candidate, monitor, tmp_path/'without_helper',
                   assert_state_correspondence=False)
    assert result['proven'] and result['initial_state']['paired_state_bits'] == 4
    miter = json.loads((tmp_path/'without_helper/miter.json').read_text())['modules']['TemporalMiter']
    assert '$pscorr_initial_state_invariant' not in miter['cells']
    assume = miter['cells']['$pscorr_initial_state_assume']
    assert assume['type'] == '$assume'
    assert assume['connections']['EN'] == miter['cells']['$pscorr_initial_state_enable']['connections']['Y']
    assert sum(c['type'] == '$assert' for c in miter['cells'].values()) == 1
    candidate.write_text(candidate.read_text().replace('q <= d;', "q <= d ^ 4'd1;"))
    negative = proof(reference, candidate, monitor, tmp_path/'functional_negative',
                     assert_state_correspondence=False)
    assert not negative['proven'] and not proof_passed(negative['base'])


def test_arbitrary_state_helper_does_not_assume_future_equality(tmp_path):
    reference, candidate, monitor = state_pair(tmp_path)
    candidate.write_text(candidate.read_text().replace('q <= d;', "q <= d ^ 4'd1;"))
    result = proof(reference, candidate, monitor, tmp_path/'state_transition_negative')
    assert not result['proven'] and not proof_passed(result['base'])


def test_no_observation_assertion_cannot_certify(tmp_path):
    reference, candidate, monitor = state_pair(tmp_path)
    monitor.write_text(monitor.read_text().replace('always @* assert(a == b);', ''))
    result = proof(reference, candidate, monitor, tmp_path/'no_assertion')
    assert not result['proven'] and 'error' in result


def test_status_gate_rejects_bounded_timeout_and_failed_process(tmp_path):
    log = tmp_path/'solver.log'
    log.write_text('Status: PASSED\n')
    assert not proof_passed({'timeout':True,'returncode':0,'log':str(log)})
    assert not proof_passed({'timeout':False,'returncode':1,'log':str(log)})
    log.write_text('Status: PASSED\nStatus: FAILED\n')
    assert not proof_passed({'timeout':False,'returncode':0,'log':str(log)})
    log.write_text('No counterexample in 4 steps\n')
    assert not proof_passed({'timeout':False,'returncode':0,'log':str(log)})


def test_candidate_design_cannot_carry_its_own_assumptions(tmp_path):
    design = json.loads(elaborate(tmp_path, CONDITIONAL).read_text())
    design['modules']['Toy']['cells']['unsafe_premise'] = {
        'type':'$assume', 'parameters':{}, 'attributes':{},
        'port_directions':{'A':'input','EN':'input'},
        'connections':{'A':['0'],'EN':['1']}}
    with pytest.raises(ValueError, match='formal premises'):
        export_design(design, 'Toy', 'ToyCandidate', tmp_path/'forbidden.v', TOOLS['yosys'], 20)
    assert not (tmp_path/'forbidden.v').exists()


def test_proof_input_changed_during_solver_run_is_rejected(tmp_path, monkeypatch):
    reference, candidate, monitor = state_pair(tmp_path)
    original_run = temporal.run_command
    def change_after_induction(argv, logfile, timeout):
        result = original_run(argv, logfile, timeout)
        if '-i' in argv:
            monitor.write_text(monitor.read_text()+'\n// changed after solver input snapshot\n')
        return result
    monkeypatch.setattr(temporal, 'run_command', change_after_induction)
    result = proof(reference, candidate, monitor, tmp_path/'changed_input')
    assert proof_passed(result['base']) and proof_passed(result['induction'])
    assert not result['proven'] and result['error'] == 'harness changed during proof'


ABC = shutil.which('abc') or shutil.which('yosys-abc')


@pytest.mark.skipif(not ABC, reason='ABC required for PDR')
@pytest.mark.parametrize('constrain_tag', [True, False])
def test_pdr_assumption_polarity_and_relaxed_negative(tmp_path, constrain_tag):
    design = json.loads(elaborate(tmp_path, CONDITIONAL).read_text())
    original = copy.deepcopy(design)
    candidate = next(c for c in equality_candidates(design, 'Toy') if c['retained_low_bits'] == 2)
    reference, modified = export_pair(tmp_path, design, candidate)
    monitor = harness(tmp_path, constrain_tag=constrain_tag)
    before = {p: digest(p) for p in (reference, modified, monitor)}
    result = proof(reference, modified, monitor, tmp_path/'pdr', engine='pdr', abc=ABC)
    assert result['proven'] is constrain_tag, result
    assert result['method'] == 'abc-pdr-shared-miter'
    assert result['aig_constraints'] > 0 and result['aig_bad_properties'] > 0
    assert 'fold; orpos; pdr' in result['pdr']['argv'][-1]
    assert 'occurrences of constant undef bits with constant zero' not in Path(result['aig_export']['log']).read_text()
    assert design == original
    assert all(digest(p) == value for p, value in before.items())
    if constrain_tag:
        assert 'Property proved.' in Path(result['pdr']['log']).read_text()
    else:
        assert 'Property proved.' not in Path(result['pdr']['log']).read_text()


@pytest.mark.skipif(not ABC, reason='ABC required for PDR')
def test_pdr_rejects_late_counterexample_beyond_requested_depth(tmp_path):
    source = '''module Toy(input clk, output hit);
      reg [3:0] age = 0;
      always @(posedge clk) age <= age + 1;
      assign hit = (age == 4'd11);
    endmodule'''
    design = json.loads(elaborate(tmp_path, source).read_text())
    candidate = next(c for c in equality_candidates(design, 'Toy') if c['retained_low_bits'] == 2)
    reference, modified = export_pair(tmp_path, design, candidate)
    monitor = tmp_path/'harness.sv'
    monitor.write_text('''module TemporalMiter(input clk);
      wire a,b; Toy reference(clk,a); ToyCandidate candidate(clk,b);
      always @* assert(a == b);
    endmodule''')
    result = proof(reference, modified, monitor, tmp_path/'late_pdr', depth=2, engine='pdr', abc=ABC)
    assert not result['proven'] and 'pdr' in result, result


@pytest.mark.skipif(not ABC, reason='ABC required for PDR')
def test_pdr_preserves_undefined_combinational_values(tmp_path):
    reference, candidate, monitor = tmp_path/'reference.v', tmp_path/'candidate.v', tmp_path/'harness.sv'
    reference.write_text("module Toy(input clk, output q); assign q = 1'bx; endmodule\n")
    candidate.write_text("module ToyCandidate(input clk, output q); assign q = 1'b0; endmodule\n")
    monitor.write_text('''module TemporalMiter(input clk);
      wire a,b; Toy reference(clk,a); ToyCandidate candidate(clk,b);
      always @* assert(a == b);
    endmodule''')
    result = proof(reference, candidate, monitor, tmp_path/'undefined', engine='pdr', abc=ABC)
    assert not result['proven'] and 'pdr' in result, result
    assert 'occurrences of constant undef bits with constant zero' not in Path(result['aig_export']['log']).read_text()


@pytest.mark.parametrize('logtext,returncode,timeout', [
    ('Property proved.\n', 1, False),
    ('Property proved.\n', 0, True),
    ('Property proved.\nProperty proved.\n', 0, False),
    ('Property proved.\nError: reader failed\n', 0, False),
    ('Property proved.\nUndecided\n', 0, False),
    ('Property proved.\nOutput 0 of miter "contradiction" was asserted in frame 3.\n', 0, False),
    ('No counterexample in 20 frames\n', 0, False),
])
def test_pdr_status_gate_is_fail_closed(tmp_path, monkeypatch, logtext, returncode, timeout):
    reference, candidate, monitor = state_pair(tmp_path)
    original_run = temporal.run_command
    def fake_pdr(argv, logfile, limit):
        if argv[0] == 'mock-abc':
            logfile.write_text(logtext)
            return {'argv':argv, 'log':str(logfile), 'returncode':returncode, 'timeout':timeout}
        return original_run(argv, logfile, limit)
    monkeypatch.setattr(temporal, 'run_command', fake_pdr)
    result = proof(reference, candidate, monitor, tmp_path/'pdr_status', engine='pdr', abc='mock-abc')
    assert 'pdr' in result, result
    assert not result['proven']


@pytest.mark.parametrize('bad_header', [
    'aig 1 0 0 1 0 1 0',  # Ordinary outputs are not safety assertions.
    'aig 1 0 0 0 0 0 1',  # Assumptions alone do not certify anything.
    'aig 1 0 0 0 0 1 1 1 0',  # Justice/liveness is unsupported.
])
def test_pdr_rejects_wrong_property_boundary(tmp_path, monkeypatch, bad_header):
    reference, candidate, monitor = state_pair(tmp_path)
    checked = temporal.checked_yosys
    def replace_header(yosys, script, directory, name, timeout):
        result = checked(yosys, script, directory, name, timeout)
        if name == 'aig_export':
            (directory/'miter.aig').write_bytes((bad_header+'\n').encode())
        return result
    monkeypatch.setattr(temporal, 'checked_yosys', replace_header)
    result = proof(reference, candidate, monitor, tmp_path/'bad_boundary', engine='pdr', abc='never-called')
    assert not result['proven'] and 'pdr' not in result
    assert 'safety assertions' in result['error']
