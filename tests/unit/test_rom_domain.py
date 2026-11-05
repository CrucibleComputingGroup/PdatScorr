"""Source extraction guards and retained SMT witness parsing; no solver runs."""
import hashlib
import importlib.util
import json
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
APP = ROOT / 'experiments/bounded_dynamic/len5/application_screen'
EVIDENCE = APP / 'evidence/rom_domain_v2'
spec = importlib.util.spec_from_file_location('rom_domain', APP / 'rom_domain.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


def fixture():
    source = (EVIDENCE / 'AdmissionScreen.sv').read_text()
    ports = json.loads((EVIDENCE / 'core_ports.json').read_text())
    words = [int(x, 16) for x in json.loads((EVIDENCE / 'summary.json').read_text())['domain_words']]
    return source, ports, words


def test_exact_source_reproduces_frozen_checker_without_extra_premises():
    source, ports, words = fixture()
    checker, audit = module.extract_producer(source, ports, words, True)
    assert checker == (EVIDENCE / 'positive/RomDomain.sv').read_text()
    assert audit == json.loads((EVIDENCE / 'positive/extraction.json').read_text())
    assert len(audit['arbitrary_core_output_ports']) == 23
    assert audit['internal_assumptions_added'] == 0


@pytest.mark.parametrize('change', ['extra_assertion', 'extra_assumption', 'changed_port_width'])
def test_unexpected_harness_changes_fail_closed(change):
    source, ports, words = fixture()
    if change == 'extra_assertion':
        source = source.replace('endmodule', 'always @* assert (rst_ni);\nendmodule')
    elif change == 'extra_assumption':
        source = source.replace('endmodule', 'always @* assume (instr_req_o);\nendmodule')
    else:
        ports['instr_addr_o']['bits'].pop()
    with pytest.raises(AssertionError):
        module.extract_producer(source, ports, words, True)


@pytest.mark.parametrize('name,word,fault', [
    ('arbitrary_fault_payload', 1, 1), ('extra_rom_word', 0xdeadbeef, 0)])
def test_negative_trace_contains_actual_output_failure_without_terminal_phantom(name, word, fault):
    rows = module.witness_rows(EVIDENCE / name / 'counterexample.vcd')
    assert [row['smt_step'] for row in rows] == [0, 1, 2, 3]
    assert rows[-1]['rst_ni'] == rows[-1]['observed_valid'] == 1
    assert rows[-1]['observed_word'] == word and rows[-1]['observed_fault'] == fault
    recorded = json.loads((EVIDENCE / name / 'counterexample.json').read_text())
    assert rows == recorded['rows']
    assert recorded['failing_external_responses'] == [rows[-1]]


def test_frozen_sources_models_and_logs_match_summary_hashes():
    meta = json.loads((EVIDENCE / 'summary.json').read_text())
    pairs = [('AdmissionScreen.sv', meta['source_harness_sha256']),
             ('program.hex', meta['rom_image_sha256']), ('program_rom.py', meta['rom_helper_sha256']),
             ('core_ports.json', meta['core_ports_sha256']), ('source_summary.json', meta['source_summary_sha256'])]
    for variant in meta['variants']:
        prefix = variant['name'] + '/'
        pairs += [(prefix + name, variant[key]) for name, key in [
            ('source_harness.sv', 'source_harness_sha256'), ('RomDomain.sv', 'checker_sha256'),
            ('model.smt2', 'smt_sha256'), ('model.json', 'model_json_sha256')]]
        for run in ('prepare', 'base', 'induction'):
            if run in variant:
                pairs.append((prefix + Path(variant[run]['log']).name, variant[run]['log_sha256']))
    for name, expected in pairs:
        assert hashlib.sha256((EVIDENCE / name).read_bytes()).hexdigest() == expected
