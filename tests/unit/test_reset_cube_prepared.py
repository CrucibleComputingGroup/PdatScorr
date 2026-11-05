"""Explicit cube opt-in cannot bypass native/prepare-only prerequisite guards."""
from pathlib import Path
import sys
import pytest

ROOT=Path(__file__).resolve().parents[2]
APP=ROOT/'experiments/bounded_dynamic/len5/application_screen'
sys.path[:0]=[str(ROOT),str(APP)]
import formal_screen
import reset_cube_prepared as validator

PREP=Path('/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build/harvard_rom_register_status_cube_native_prepare_v1')


@pytest.mark.parametrize('extra,message',[
    (['--reset-cube-lemmas','missing'],'require each other'),
    (['--reset-cube-reference-prepared','missing'],'require each other'),
    (['--reset-cube-lemmas','missing','--reset-cube-reference-prepared','missing'],'requires the closed register-status'),
])
def test_missing_chain_rejected_before_output_creation(monkeypatch,capsys,extra,message):
    monkeypatch.setattr(sys,'argv',['formal_screen.py','--disassembly','missing','--output','must_not_create',
        '--engine','prepare',*extra])
    with pytest.raises(SystemExit) as error:formal_screen.main()
    assert error.value.code==2 and message in capsys.readouterr().err
    assert not Path('must_not_create').exists()


@pytest.mark.parametrize('engine,mode',[('pdr','none'),('prepare','alu_mul')])
def test_full_cube_chain_still_rejects_solver_and_arithmetic_abstraction(monkeypatch,capsys,engine,mode):
    monkeypatch.setattr(sys,'argv',['formal_screen.py','--disassembly','missing','--output','must_not_create',
        '--program-hex','missing','--zero-fault-data','--decoder-certificate','missing','--word-domain-lemmas',
        '--rom-domain-proof','missing','--inactive-fu-lemmas','missing','--register-status-lemmas','missing',
        '--reset-cube-lemmas','missing','--reset-cube-reference-prepared','missing',
        '--engine',engine,'--datapath-abstraction',mode])
    with pytest.raises(SystemExit) as error:formal_screen.main()
    assert error.value.code==2 and '--register-status-lemmas requires' in capsys.readouterr().err
    assert not Path('must_not_create').exists()


def test_actual_combined_preparation_retains_native_bytes_and_properties():
    if not PREP.exists():pytest.skip('Combined preparation not yet available')
    record=validator.validate_reset_cube_prepared(PREP)
    assert record['core_json_sha256']=='2426b17743dfc23d806d5c544f9c6ebbc722909ed01442f0cb41403a11ad4b48'
    assert record['query_property_counts']=={'assert':3,'assume':48,'cover':0}
    assert len(record['reset_cube_import']['composition']['existing_predicate_cells_preserved'])==479
