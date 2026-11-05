"""Delta-only cube composition and proof-export replay; no solver query."""
import copy
import json
from pathlib import Path
import sys

import pytest

ROOT = Path(__file__).resolve().parents[2]
APP = ROOT/'experiments/bounded_dynamic/len5/application_screen'
sys.path[:0] = [str(ROOT), str(APP)]
import reset_cube_import as importer

BUILD = Path('/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build')
YOSYS = Path('/home/allenjin/Projects/DAC_pscorr/tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys')


@pytest.fixture(scope='module')
def actual():
    prepared = BUILD/'harvard_rom_register_status_native_prepare_v1'
    run = BUILD/'reset_cube_native_fixedpoint_v1'
    review = APP/'review/reset_cube_fixedpoint_v1/review.json'
    if not all(p.exists() for p in (prepared/'summary.json', run/'summary.json', review, YOSYS)):
        pytest.skip('Frozen native theorem sources unavailable')
    record = importer.read(prepared/'summary.json')
    return run, prepared, record, importer.read(Path(record['query_core_path']))


def arguments(actual, tmp_path):
    run, prepared, record, current = actual
    return (run, prepared, current, tmp_path/'import'), dict(yosys=YOSYS,
        current_records={name: record[name] for name in importer.STATUSES},
        current_harness=prepared/'AdmissionScreen.sv', current_native_core=prepared/'core.json')


def test_actual_cube_delta_preserves_47_predicates_and_replays_proofs(actual, tmp_path):
    args, kwargs = arguments(actual, tmp_path)
    result, record = importer.import_reset_cube(*args, **kwargs)
    current = actual[3]['modules']['datapath']
    changed = result['modules']['datapath']
    assert record['assumptions_added'] == 0 and record['proved_reset_bits_substituted'] == 583
    assert len(current['cells'])-len(changed['cells']) == 42
    assert current['ports'] == changed['ports']
    assert sum(c['type'] == '$assume' for c in changed['cells'].values()) == 47
    for name in record['composition']['existing_predicate_cells_preserved']:
        assert current['cells'][name] == changed['cells'][name]
    assert len(record['composition']['existing_predicate_cells_preserved']) == 479
    assert len(record['composition']['cdb_arbitration_bits_substituted']) == 8
    assert record['composition']['preceding_register_status_constants_preserved'] == 275
    for proof in record['export_replays'].values():
        assert proof['byte_identical'] and proof['solver_rerun'] is False
        for execution in proof['export_replays']:
            script = Path(execution['argv'][-1]).read_text()
            assert not any(line.startswith(('sat ', 'tee ')) for line in script.splitlines())
    importer.verify_dependencies(record)


def test_missing_independent_review_rejected_before_exports(actual, tmp_path, monkeypatch):
    args, kwargs = arguments(actual, tmp_path)
    review = tmp_path/'review.json'
    review.write_text(json.dumps({'status': 'pending'}))
    kwargs['review_path'] = review
    monkeypatch.setattr(importer, 'replay_obligation', lambda *a, **k: pytest.fail('Unreviewed theorem reached exports'))
    with pytest.raises(ValueError, match='independent cube review'):
        importer.import_reset_cube(*args, **kwargs)


def test_wholesale_old_cube_graph_is_not_current_query(actual, tmp_path, monkeypatch):
    args, kwargs = arguments(actual, tmp_path)
    changed = importer.read(actual[0]/'query_only_patch.json')
    args = (args[0], args[1], changed, args[3])
    monkeypatch.setattr(importer, 'replay_obligation', lambda *a, **k: pytest.fail('Wrong graph reached exports'))
    with pytest.raises(ValueError, match='validated48-premise reference'):
        importer.import_reset_cube(*args, **kwargs)


def test_mutated_derived_predicate_is_rejected(actual):
    run, _, record, current = actual
    changed = copy.deepcopy(current)
    name = record['native_word_domain_import']['added_cells'][0]
    changed['modules']['datapath']['cells'][name]['connections']['B'][0] = '1'
    with pytest.raises(ValueError, match='Current graph is not the exact closed source'):
        importer.compose_delta(importer.read(run/'source.json'), changed, importer.read(run/'selected_words.json'), record)


def test_changed_transitive_proof_is_rejected(tmp_path):
    path = tmp_path/'sat.log'
    path.write_text('original proof')
    record = {'proof_dependencies_sha256': {str(path): importer.digest(path)}}
    importer.verify_dependencies(record)
    path.write_text('changed proof')
    with pytest.raises(ValueError, match='dependency changed'):
        importer.verify_dependencies(record)
