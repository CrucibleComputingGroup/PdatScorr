"""Native-only GLA entry guards and post-run dependency closure."""
import copy
import json
from pathlib import Path
import sys

import pytest

ROOT = Path(__file__).resolve().parents[2]
APP = ROOT/'experiments/bounded_dynamic/len5/application_screen'
sys.path[:0] = [str(ROOT), str(APP)]
import native_gate_solver as driver

PREPARED = Path('/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build/harvard_rom_inactive_fu_native_prepare_v1')


@pytest.fixture
def fixture(tmp_path, monkeypatch):
    dep = tmp_path/'proof.log'; dep.write_text('proved')
    deps = {str(dep):driver.digest(dep)}
    facts = dict(status='inactive_fu_reset_facts_replayed', query_only=True, accepted_optimization=False,
        native_hardware_export_unchanged=True, assumptions_added=0, new_environmental_premises=[],
        reset_substitutions=list(range(1761)), proof_dependencies_sha256=deps)
    model = dict(abstraction_mode='none', datapath_abstraction=None, abstraction_helper_sha256=None,
        query_property_counts={'assert':3,'assume':8,'cover':0}, instruction_model='immutable_rom',
        instruction_fault_payload='zero', native_hardware_contains_formal_properties=False,
        certified_decoder_import={'status':'certificate_replayed_and_native_substitution_bound'},
        native_word_domain_import={'status':'seven_proved_native_word_domains_imported','proof_dependencies_sha256':deps.copy()},
        external_rom_domain_import={'status':'exact_external_rom_domain_certified','proof_dependencies_sha256':deps.copy()},
        inactive_fu_import=facts, query_core_path=str(tmp_path/'inactive_query_core.json'),
        core_json_sha256='native', query_core_sha256='query', aig_sha256='aig')
    (tmp_path/'summary.json').write_text(json.dumps(model))
    monkeypatch.setattr(driver, 'validate_prepared', lambda directory:copy.deepcopy(model))
    return tmp_path, model, dep


@pytest.mark.parametrize('mutation,match', [
    (lambda m:m.update(abstraction_mode='alu_mul'), 'Native arithmetic'),
    (lambda m:m.update(datapath_abstraction={'changed':True}), 'Native arithmetic'),
    (lambda m:m['query_property_counts'].update(assume=9), 'three assertions'),
    (lambda m:m['inactive_fu_import'].update(new_environmental_premises=['bound']), 'scope changed'),
    (lambda m:m.update(query_core_path='/tmp/other.json'), 'exact inactive-FU'),
    (lambda m:m['native_word_domain_import'].update(proof_dependencies_sha256={}), 'transitive dependencies'),
])
def test_rejects_scope_changes(fixture, mutation, match):
    path, model, _ = fixture
    mutation(model)
    with pytest.raises(ValueError, match=match):driver.validate_native(path)


def test_rejects_changed_transitive_proof(fixture):
    path, _, dep = fixture; dep.write_text('changed')
    with pytest.raises(ValueError, match='Proof dependency changed'):driver.validate_native(path)


@pytest.mark.parametrize('change', [False,True])
def test_postrun_dependency_verification(fixture, monkeypatch, change):
    path, _, dep = fixture
    def fake_gla(aig, output, **kwargs):
        output.mkdir()
        if change:dep.write_text('changed during solver')
        return dict(status='unknown', input_aig_sha256='aig')
    monkeypatch.setattr(driver, 'run_gla', fake_gla)
    result = driver.run_native(path, path/'run', timeout=1)
    assert result['status'] == ('error' if change else 'unknown')
    assert result['post_run_dependencies_verified'] is not change
    assert (path/'run/wrapper_sources/native_gate_solver.py').exists()


def test_actual_frozen_preparation_all_dependencies():
    if not PREPARED.exists():pytest.skip('External source-bound preparation unavailable')
    model, dependencies = driver.validate_native(PREPARED)
    assert model['aig_header'][3:6] == ['22024','0','522336']
    assert len(dependencies) == 269
