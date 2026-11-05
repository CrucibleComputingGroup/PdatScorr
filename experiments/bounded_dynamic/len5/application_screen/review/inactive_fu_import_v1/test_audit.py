"""Negative checks for the independent integration graph/provenance audit."""
import copy
import importlib.util
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('inactive_import_independent_audit', HERE / 'audit.py')
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)


@pytest.fixture(scope='module')
def graphs():
    if not (audit.PREPARED / 'summary.json').exists():
        pytest.skip('Frozen external models unavailable')
    return [audit.read(audit.PREPARED / name) for name in
            ('core.json', 'lemma_core.json', 'inactive_query_core.json', 'abstract_query_core.json', 'summary.json')]


def test_frozen_whole_graph(graphs):
    result = audit.check_graph(*graphs)
    assert result['reset_bits'] == 1761 and result['unchanged_word_lemma_cells'] == 119


def test_unproved_cell_change_is_rejected(graphs):
    altered = copy.deepcopy(graphs[2])
    altered['modules']['datapath']['cells']['$pscorr_review_hidden_assumption'] = {
        'type': '$assume', 'port_directions': {'A': 'input', 'EN': 'input'},
        'connections': {'A': ['1'], 'EN': ['1']}, 'parameters': {}, 'attributes': {}}
    with pytest.raises(ValueError, match='Composed graph differs'):
        audit.check_graph(graphs[0], graphs[1], altered, graphs[3], graphs[4])


def test_extra_abstraction_is_rejected(graphs):
    altered = copy.deepcopy(graphs[3])
    altered['modules']['datapath']['ports']['probe_index']['bits'][0] = '1'
    with pytest.raises(ValueError, match='Additional abstraction mutation'):
        audit.check_graph(graphs[0], graphs[1], graphs[2], altered, graphs[4])


def test_non_native_reset_replacement_is_rejected(graphs):
    substitutions = {int(bit): value for bit, value in graphs[4]['inactive_fu_import']['reset_substitutions'].items()}
    substitutions[91687] = '1'
    with pytest.raises(ValueError, match='Wrong reset constant'):
        audit.graph_rewrite(graphs[0], substitutions)


def test_nested_dependency_mutation_is_rejected(tmp_path):
    log = tmp_path / 'proof.log'
    log.write_text('original induction result')
    dependencies = {str(log): audit.sha(log)}
    audit.verify(dependencies)
    log.write_text('changed induction result')
    with pytest.raises(ValueError, match='Dependency changed'):
        audit.verify(dependencies)
