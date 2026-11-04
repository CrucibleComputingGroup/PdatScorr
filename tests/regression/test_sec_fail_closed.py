"""Focused checker-gate regression; no processor synthesis or simulation."""
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
from types import SimpleNamespace

import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from odc.sec_checker import SecChecker, SecResult, SecStatus
from odc.constraint_analyzer import ConstantBit
from odc.report_generator import OdcTestResult, ReportGenerator


def aig(path, inverted=False, redundant=False):
    """Handwritten one-register binary AIGER fixture: q_next=input, output=q."""
    if redundant:
        data = b'aig 3 1 1 1 1\n2 0\n6\n' + bytes([2, 0])
    else:
        data = b'aig 2 1 1 1 0\n' + (b'3 0\n' if inverted else b'2 0\n') + b'4\n'
    path.write_bytes(data+b'i0 input\nl0 state\no0 output\nc\nchecker fixture\n')
    return path


@pytest.fixture
def pair(tmp_path):
    return aig(tmp_path/'reference.aig'), aig(tmp_path/'candidate.aig', redundant=True)


@pytest.mark.parametrize('output,status', [
    ('UNSAT\n', SecStatus.UNKNOWN),
    ('No output asserted in 8 frames\n', SecStatus.UNKNOWN),
    ('Networks are UNDECIDED.\n', SecStatus.UNKNOWN),
    ('Networks are equivalent.\nError: failed output\n', SecStatus.ERROR),
    ('Networks are equivalent.\nABC: command failed\n', SecStatus.ERROR),
    ('Networks are equivalent.\nTimeout\n', SecStatus.TIMEOUT),
    ('Networks are equivalent.\nNetworks are NOT EQUIVALENT.\n', SecStatus.ERROR),
    ('Networks are equivalent. Time=0.01\n', SecStatus.EQUIVALENT),
    ('Networks are NOT EQUIVALENT after simulation.\n', SecStatus.NOT_EQUIVALENT),
])
def test_final_status_is_required(output, status):
    assert SecChecker()._parse_abc_output(output)[0] == status


def test_failed_process_cannot_authorize(pair, monkeypatch):
    monkeypatch.setattr(subprocess, 'run', lambda *a, **kw:
                        SimpleNamespace(returncode=1, stdout='Networks are equivalent.\n'))
    result = SecChecker().check_equivalence(*pair)
    assert result.status == SecStatus.ERROR and not result.is_equivalent


def test_explicit_pair_and_provenance(pair, monkeypatch):
    seen = []
    def run(command, **kwargs):
        seen.append(command)
        return SimpleNamespace(returncode=0, stdout='Networks are equivalent.\n')
    monkeypatch.setattr(subprocess, 'run', run)
    result = SecChecker().check_equivalence(*pair)
    assert result.is_equivalent and len(result.input_sha256) == 2
    script = seen[0][-1]
    assert script.startswith('dsec ') and all(str(p.resolve()) in script for p in pair)
    assert 'read_aiger' not in script and 'constr' not in script


def test_constraints_rejected_before_checker(pair, monkeypatch):
    pair[1].write_bytes(pair[1].read_bytes().replace(b'aig 3 1 1 1 1\n', b'aig 3 1 1 1 1 0 1\n'))
    monkeypatch.setattr(subprocess, 'run', lambda *a, **kw: pytest.fail('must not invoke ABC'))
    result = SecChecker().check_equivalence(*pair)
    assert result.status == SecStatus.ERROR and 'shared-contract' in result.abc_output


def test_arbitrary_initial_state_rejected_before_checker(pair, monkeypatch):
    pair[0].write_bytes(pair[0].read_bytes().replace(b'2 0\n', b'2 4\n'))
    monkeypatch.setattr(subprocess, 'run', lambda *a, **kw: pytest.fail('must not invoke ABC'))
    result = SecChecker().check_equivalence(*pair)
    assert result.status == SecStatus.ERROR and 'initial state' in result.abc_output


def test_timeout_does_not_promote_partial_success(pair, monkeypatch):
    def run(*args, **kwargs):
        raise subprocess.TimeoutExpired(args[0], 1, output=b'Networks are equivalent.\n')
    monkeypatch.setattr(subprocess, 'run', run)
    result = SecChecker().check_equivalence(*pair)
    assert result.status == SecStatus.TIMEOUT and not result.is_equivalent


def test_changed_input_invalidates_proof(pair, monkeypatch):
    def run(*args, **kwargs):
        pair[1].write_bytes(pair[1].read_bytes()+b'changed\n')
        return SimpleNamespace(returncode=0, stdout='Networks are equivalent.\n')
    monkeypatch.setattr(subprocess, 'run', run)
    assert SecChecker().check_equivalence(*pair).status == SecStatus.ERROR


def test_identical_path_and_unsafe_command_path_rejected(pair, monkeypatch):
    monkeypatch.setattr(subprocess, 'run', lambda *a, **kw: pytest.fail('must not invoke ABC'))
    assert SecChecker().check_equivalence(pair[0], pair[0]).status == SecStatus.ERROR
    assert SecChecker().check_equivalence(pair[0], pair[0].with_name('x;quit.aig')).status == SecStatus.ERROR


def test_report_rejects_synthetic_and_unqualified_equivalence(tmp_path):
    results = [SecResult(SecStatus.EQUIVALENT, 0),
               SecResult(SecStatus.EQUIVALENT, 0, proof_completed=True,
                         proof_method='fixture', returncode=0, synthetic=True)]
    ReportGenerator(tmp_path/'input.dsl', tmp_path).generate_reports([
        OdcTestResult(ConstantBit('shamt', i, 0), result) for i, result in enumerate(results)])
    report = json.loads((tmp_path/'odc_report.json').read_text())
    assert report['metadata']['confirmed_odcs'] == 0
    assert report['metadata']['synthetic_results'] == 1
    assert not any(row['is_odc'] for row in report['results'])


def test_bounded_mux_and_legacy_sat_cannot_authorize():
    spec = importlib.util.spec_from_file_location('odc_analysis_under_test', ROOT/'scripts/odc_analysis.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    cases = module.require_inductive_mux_evidence([SimpleNamespace(sec_verified=True, reason='BMC passed')])
    assert not cases[0].sec_verified
    assert not SecChecker().check_miter_is_zero(Path('unused.aig')).is_equivalent


def test_real_abc_equivalent_and_observable_mutation(pair, tmp_path):
    abc = shutil.which('yosys-abc') or shutil.which('abc')
    if not abc:
        pytest.skip('ABC unavailable; status and report checks still run')
    checker = SecChecker(abc, timeout_sec=10)
    good = checker.check_equivalence(*pair)
    assert good.is_equivalent, good.abc_output
    bad = checker.check_equivalence(pair[0], aig(tmp_path/'observable_mutation.aig', inverted=True))
    assert bad.status == SecStatus.NOT_EQUIVALENT and not bad.is_equivalent, bad.abc_output
