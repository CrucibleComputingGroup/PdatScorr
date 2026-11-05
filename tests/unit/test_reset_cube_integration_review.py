"""Independent combined-query reconstruction and fail-closed checks, no solver."""
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import pytest

ROOT=Path(__file__).resolve().parents[2]
APP=ROOT/'experiments/bounded_dynamic/len5/application_screen'
spec=importlib.util.spec_from_file_location('independent_cube_import',APP/'review/reset_cube_import_v1/audit.py')
audit=importlib.util.module_from_spec(spec);spec.loader.exec_module(audit)
from reset_cube_prepared import validate_reset_cube_prepared


@pytest.fixture(scope='module')
def reviewed():
    if not (audit.PREPARED/'summary.json').exists():pytest.skip('Frozen combined preparation unavailable')
    return audit.reconstruct()


def test_exact_delta_has_no_predicate_port_or_hardware_replacement(reviewed):
    assert reviewed['exact_graph_reconstruction']
    assert len(reviewed['word_cells'])==119 and len(reviewed['RD_cells'])==360
    assert len(reviewed['eight_CDB_arbiter_bits_removed'])==8
    assert reviewed['record']['query_property_counts']=={'assert':3,'assume':48,'cover':0}


def test_both_replayed_obligations_have_no_solver_command(reviewed):
    for result in reviewed['cube_record']['export_replays'].values():
        assert result['byte_identical'] and not result['solver_rerun']
        for run in result['export_replays']:
            text=Path(run['argv'][-1]).read_text()
            assert not any(line.lstrip().startswith(('sat ','tee ','abc ')) for line in text.splitlines())


@pytest.mark.parametrize('change',['premise','bits','engine'])
def test_validator_rejects_unqualified_summary_before_artifact_reads(tmp_path,reviewed,change):
    record=copy.deepcopy(reviewed['record'])
    if change=='premise':record['reset_cube_import']['assumptions_added']=1
    elif change=='bits':record['reset_cube_import']['proved_reset_bits_substituted']=584
    else:record['engine']='pdr'
    (tmp_path/'summary.json').write_text(json.dumps(record))
    with pytest.raises(ValueError):validate_reset_cube_prepared(tmp_path)


@pytest.mark.parametrize('case',['missing_reference','missing_register_status','backend'])
def test_cube_cli_rejects_unqualified_mode_before_any_output_or_tool(tmp_path,case):
    output=tmp_path/'forbidden';missing=str(tmp_path/'absent')
    command=[sys.executable,str(APP/'formal_screen.py'),'--disassembly',missing,'--output',str(output),
        '--program-hex',missing,'--zero-fault-data','--decoder-certificate',missing,
        '--word-domain-lemmas','--rom-domain-proof',missing,'--inactive-fu-lemmas',missing,
        '--reset-cube-lemmas',missing,'--engine','pdr' if case=='backend' else 'prepare',
        '--yosys','/must/not/run','--abc','/must/not/run']
    if case!='missing_reference':command+=['--reset-cube-reference-prepared',missing]
    if case!='missing_register_status':command+=['--register-status-lemmas',missing]
    run=subprocess.run(command,text=True,capture_output=True,timeout=10)
    assert run.returncode==2 and not output.exists()
    expected='--register-status-lemmas requires' if case=='backend' else '--reset-cube-lemmas'
    assert expected in run.stderr
