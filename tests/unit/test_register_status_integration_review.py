"""Independent prepared-query graph/encoding checks; never invokes a solver."""
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import pytest

ROOT=Path(__file__).resolve().parents[2]
APP=ROOT/'experiments/bounded_dynamic/len5/application_screen'
AUDIT=APP/'review/register_status_integration_v2/audit.py'
spec=importlib.util.spec_from_file_location('independent_register_status_integration',AUDIT)
audit=importlib.util.module_from_spec(spec);spec.loader.exec_module(audit)
from register_status_prepared import validate_register_status_prepared


@pytest.fixture(scope='module')
def reconstructed():
    if not (audit.PREPARED/'summary.json').exists():pytest.skip('Original prepared query artifacts unavailable')
    return audit.reconstruct()


def test_independent_fullgraph_reconstruction_and_both_dependency_checks(reconstructed):
    assert reconstructed['exact_graph_reconstruction']
    assert reconstructed['domain_dependencies_verified_before_and_after']
    assert len(reconstructed['record']['native_word_domain_import']['proof_dependencies_sha256'])==1964


def test_all_forty_predicates_encode_exact_unsigned_visible_domains(reconstructed):
    module=audit.read(audit.PREPARED/'register_status_query_core.json')['modules']['datapath']
    for index,field in enumerate(reconstructed['fields']):
        values=[];wires=[]
        for j in range(7):
            cell=module['cells'][f'$pscorr_rd_lemma_{index}_value_{j}']
            assert cell['type']=='$eq' and cell['connections']['A']==field['bits']
            assert cell['parameters']['A_SIGNED']==cell['parameters']['B_SIGNED']==0
            values.append(sum(int(bit)<<k for k,bit in enumerate(cell['connections']['B'])))
            wires+=cell['connections']['Y']
        reducer=module['cells'][f'$pscorr_rd_lemma_{index}_or']
        premise=module['cells'][f'$pscorr_rd_lemma_{index}_assume']
        assert reducer['type']=='$reduce_or' and reducer['connections']['A']==wires
        assert premise['connections']=={'A':reducer['connections']['Y'],'EN':['1']}
        assert premise['attributes']['pscorr_proved_rd_field']==field['cell']
        for value in range(32):
            assert any(value==literal for literal in values)==(value in {0,5,8,9,10,11,18})


@pytest.mark.parametrize('mutation',['engine','counts','RF'])
def test_prepared_validator_fails_closed_before_artifact_access(tmp_path,reconstructed,mutation):
    record=copy.deepcopy(reconstructed['record'])
    if mutation=='engine':record['engine']='pdr'
    elif mutation=='counts':record['query_property_counts']['assume']=49
    else:record['register_status_import']['rf_candidate_substituted']=True
    (tmp_path/'summary.json').write_text(json.dumps(record))
    with pytest.raises(ValueError):validate_register_status_prepared(tmp_path)


@pytest.mark.parametrize('engine,abstraction',[('pdr','none'),('bmc','none'),('prepare','alu_mul')])
def test_cli_rejects_backend_or_abstraction_before_output_creation(tmp_path,engine,abstraction):
    output=tmp_path/'must_not_exist'
    command=[sys.executable,str(APP/'formal_screen.py'),'--disassembly',str(tmp_path/'missing'),
        '--output',str(output),'--program-hex',str(tmp_path/'missing'),'--zero-fault-data',
        '--decoder-certificate',str(tmp_path/'missing'),'--word-domain-lemmas',
        '--rom-domain-proof',str(tmp_path/'missing'),'--inactive-fu-lemmas',str(tmp_path/'missing'),
        '--register-status-lemmas',str(tmp_path/'missing'),'--engine',engine,
        '--datapath-abstraction',abstraction,'--yosys','/must/not/run','--abc','/must/not/run']
    result=subprocess.run(command,text=True,capture_output=True,timeout=10)
    assert result.returncode==2 and '--register-status-lemmas requires' in result.stderr
    assert not output.exists()
