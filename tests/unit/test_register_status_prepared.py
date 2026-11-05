"""The new preparation family has explicit48-premise scope, not a legacy bypass."""
import copy
from pathlib import Path
import sys
import pytest

ROOT=Path(__file__).resolve().parents[2]
APP=ROOT/'experiments/bounded_dynamic/len5/application_screen'
sys.path[:0]=[str(ROOT),str(APP)]
import formal_screen
import register_status_prepared as validator
import solve_prepared

PREP=Path('/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build/harvard_rom_register_status_native_prepare_v1')


@pytest.mark.parametrize('extra',[
    ['--engine','pdr'],
    ['--engine','prepare','--datapath-abstraction','alu_mul'],
])
def test_cli_rejects_unapproved_solver_or_payload_abstraction(monkeypatch,capsys,extra):
    argv=['formal_screen.py','--disassembly','missing','--output','must_not_create',
        '--program-hex','missing','--zero-fault-data','--decoder-certificate','missing',
        '--word-domain-lemmas','--rom-domain-proof','missing','--inactive-fu-lemmas','missing',
        '--register-status-lemmas','missing',*extra]
    monkeypatch.setattr(sys,'argv',argv)
    with pytest.raises(SystemExit) as error:formal_screen.main()
    assert error.value.code==2
    assert '--register-status-lemmas requires' in capsys.readouterr().err
    assert not Path('must_not_create').exists()


def test_actual_preparation_fullclosure_and_unchanged_native():
    if not PREP.exists():pytest.skip('External source-bound preparation unavailable')
    record=validator.validate_register_status_prepared(PREP)
    assert record['core_json_sha256']=='2426b17743dfc23d806d5c544f9c6ebbc722909ed01442f0cb41403a11ad4b48'
    assert record['query_property_counts']=={'assert':3,'assume':48,'cover':0}
    assert record['register_status_import']['rf_candidate_substituted'] is False


def test_old_solver_entry_guard_still_rejects_new_family():
    if not PREP.exists():pytest.skip('External source-bound preparation unavailable')
    with pytest.raises(ValueError,match='property inventory'):
        solve_prepared.validate_prepared(PREP)


def test_extra_assumption_rejected_before_dependency_replay(monkeypatch):
    if not PREP.exists():pytest.skip('External source-bound preparation unavailable')
    original=validator.read
    def changed(path):
        record=original(path)
        if path==PREP/'summary.json':
            record=copy.deepcopy(record);record['query_property_counts']['assume']=49
        return record
    monkeypatch.setattr(validator,'read',changed)
    with pytest.raises(ValueError,match='property inventory'):
        validator.validate_register_status_prepared(PREP)
