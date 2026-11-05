"""Import validation tests; synthetic certificates are not hardware proofs."""
import copy
import importlib.util
import json
from pathlib import Path
import sys

import pytest

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
HELPER=ROOT/'experiments/bounded_dynamic/len5/application_screen/certified_decoder.py'
spec=importlib.util.spec_from_file_location('certified_decoder',HELPER)
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)


@pytest.fixture
def fixture(tmp_path,monkeypatch):
    prepared=tmp_path/'prepared';candidate_dir=tmp_path/'candidate'
    prepared.mkdir();candidate_dir.mkdir()
    original={'modules':{'datapath':{'ports':{'i':{'direction':'input','bits':[2]},'o':{'direction':'output','bits':[3]}},
        'netnames':{'i':{'bits':[2]},'o':{'bits':[3]}},
        'cells':{'decoder':{'type':'$not','connections':{'A':[2],'Y':[3]},'parameters':{},'port_directions':{'A':'input','Y':'output'}},
                 'outside':{'type':'$not','connections':{'A':[3],'Y':[4]},'parameters':{},'port_directions':{'A':'input','Y':'output'}}}}}}
    changed=copy.deepcopy(original);changed['modules']['datapath']['cells']['decoder']['connections']['A']=['0']
    native_original=prepared/'whole_core.json';native_original.write_text(json.dumps(original))
    fresh=tmp_path/'fresh.json';fresh.write_bytes(native_original.read_bytes())
    native_candidate=candidate_dir/'native_candidate.json';native_candidate.write_text(json.dumps(changed))
    certifier=tmp_path/'certifier.py';certifier.write_text('# Synthetic verifier substituted by the unit test.\n')
    cert={'status':'component_equivalence_and_domain_propagation_certified','domain':'program_alphabet',
        'external_premises':module.PREMISES.copy(),'all_decoder_external_consumers_observed':True,
        'native_ports_and_all_unmodified_cells_preserved':True,'domain_projection_cells_unchanged_by_specialization':True,
        'invalid_instruction_payload_restricted':False,'instruction_payload_during_reset_restricted':False,
        'physical_candidate_has_formal_monitors':False,'decoder_outputs':module.OUTPUTS.copy(),
        'timing_or_occupancy_premises':[],'unobserved_external_consumers':[],
        'original_state_cell_drivers_replaced':0,'domain_expression':"(instruction_i == 0) || (instruction_i == 32'h0000006f)",
        'certifier_sha256':module.digest(certifier),'native_original_sha256':module.digest(native_original),
        'native_original_json':str(native_original),'native_candidate_json':str(native_candidate),
        'native_candidate_sha256':module.digest(native_candidate),'candidate_summary':str(candidate_dir/'summary.json'),
        'domain_summary':str(tmp_path/'domain/summary.json'),'paired_proof_summary':str(tmp_path/'pair/summary.json'),
        'changed_cells':['decoder']}
    path=tmp_path/'certificate.json';path.write_text(json.dumps(cert))
    image={'bytes':4,'words':{0:0x6f},'immutable_instruction_image':True,'byte_order':'little','image_sha256':'test-image'}
    calls=[]
    def replay(argv,log,timeout):
        calls.append(argv);Path(argv[-1]).write_bytes(path.read_bytes());log.write_text('Synthetic verifier replay\n')
        return {'returncode':0,'timeout':False,'log':str(log),'argv':argv}
    monkeypatch.setattr(module,'run_command',replay)
    def invoke(**kw):
        return module.import_decoder(path,fresh,image,tmp_path/'import',certifier=certifier,
             zero_fault_data=kw.pop('zero_fault_data',True),initial_reset=kw.pop('initial_reset',True),**kw)
    return locals()


def test_replay_and_exact_native_source_binding(fixture):
    f=fixture;before=f['fresh'].read_bytes();design,record=f['invoke']()
    assert design==f['changed'] and f['fresh'].read_bytes()==before
    assert record['assumptions_added']==0 and record['native_storage_drivers_replaced']==0
    assert design['modules']['datapath']['cells']['outside']==f['original']['modules']['datapath']['cells']['outside']
    assert design['modules']['datapath']['ports']==f['original']['modules']['datapath']['ports']
    assert len(f['calls'])==1
    argv=f['calls'][0]
    assert argv[argv.index('--prepared')+1]==str(f['prepared'])
    assert argv[argv.index('--candidate')+1]==str(f['candidate_dir'])
    assert record['original_native_sha256']==module.digest(f['fresh'])
    assert record['candidate_native_sha256']==module.digest(f['native_candidate'])


@pytest.mark.parametrize('change',['withdrawn','original_hash','candidate_hash','certifier_hash','unqualified_reset'])
def test_stale_or_inapplicable_certificate_rejected_before_replay(fixture,change):
    f=fixture;cert=f['cert']
    if change=='withdrawn':cert['status']='withdrawn_pending_revalidation'
    elif change=='unqualified_reset':cert['external_premises'][1]='instr_rvalid_i -> instruction response word in declared domain'
    else:cert[{'original_hash':'native_original_sha256','candidate_hash':'native_candidate_sha256','certifier_hash':'certifier_sha256'}[change]]='0'*64
    f['path'].write_text(json.dumps(cert))
    with pytest.raises(ValueError):f['invoke']()
    assert not f['calls']


def test_semantically_same_but_different_fresh_native_source_bytes_rejected(fixture):
    f=fixture;f['fresh'].write_text(json.dumps(f['original'],indent=2))
    with pytest.raises(ValueError,match='Fresh native source'):f['invoke']()
    assert not f['calls']


@pytest.mark.parametrize('mode',['extra_word','nonzero_fault','no_reset','undefined_word'])
def test_platform_must_imply_entire_external_instruction_domain(fixture,mode):
    f=fixture;kw={}
    if mode=='extra_word':f['image']['words'][0]=0x13
    elif mode=='undefined_word':f['image']['words'][0]='x'
    elif mode=='nonzero_fault':kw['zero_fault_data']=False
    else:kw['initial_reset']=False
    with pytest.raises(ValueError):f['invoke'](**kw)
    assert not f['calls']


def test_fresh_certifier_result_must_match_every_certificate_field(fixture,monkeypatch):
    f=fixture
    def wrong(argv,log,timeout):
        changed=copy.deepcopy(f['cert']);changed['domain_expression']="(instruction_i == 0)"
        Path(argv[-1]).write_text(json.dumps(changed));return {'returncode':0,'timeout':False}
    monkeypatch.setattr(module,'run_command',wrong)
    with pytest.raises(ValueError,match='differs'):f['invoke']()


def test_candidate_changed_during_verifier_replay_is_rejected(fixture,monkeypatch):
    f=fixture
    def mutate(argv,log,timeout):
        Path(argv[-1]).write_bytes(f['path'].read_bytes())
        f['native_candidate'].write_bytes(f['native_candidate'].read_bytes()+b'\n')
        return {'returncode':0,'timeout':False}
    monkeypatch.setattr(module,'run_command',mutate)
    with pytest.raises(ValueError,match='changed during replay'):f['invoke']()


@pytest.mark.parametrize('text',[
    "(instruction_i & 32'h7f) == 32'h13", "(instruction_i == 0) || 1",
    "(instruction_i == 32'h0000006f)", "(instruction_i == 0) || (instruction_i == 32'h00000000)",
])
def test_exact_alphabet_parser_rejects_broad_or_malformed_domains(text):
    with pytest.raises(ValueError):module.exact_alphabet(text)
