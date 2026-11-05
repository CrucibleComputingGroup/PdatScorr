"""Independent, solver-free audit of the frozen native register-status evidence.

Requires the original workspace artifacts; absent artifacts are explicitly skipped.
The checks do not call the generator under review or treat bounded success as proof.
"""
import hashlib
import json
from pathlib import Path
import pytest

BUILD=Path('/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build')
RUN=BUILD/'register_status_lemmas_v2'
pytestmark=pytest.mark.skipif(not (RUN/'summary.json').is_file(),reason='Original register-status proof artifacts unavailable')


def read(path):return json.loads(path.read_text())
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


@pytest.fixture(scope='module')
def evidence():
    record=read(RUN/'summary.json')
    assert record['status']=='program_only_register_status_reset_facts_composed'
    assert record['query_only'] and not record['accepted_optimization']
    assert not record['new_environmental_premises'] and not record['timing_premises']
    for name,value in record['source_dependencies_sha256'].items():assert sha(Path(name))==value
    assert sha(RUN/'native_input.json')==record['native_input_sha256']
    assert sha(RUN/'query_only.json')==record['query_model_sha256']
    return record,read(RUN/'native_input.json'),read(RUN/'query_only.json')


def test_component_is_exact_native_cone_with_original_functional_boundary(evidence):
    record,native,_=evidence
    component=read(RUN/'component.json')['modules']['NativeRegisterStatus']
    original=native['modules']['datapath'];audit=record['native_component_audit'];prefix=audit['prefix']
    assert len(component['cells'])==506
    assert set(component['cells'])==set(audit['native_component_cells'])
    assert all(cell==original['cells'][name] for name,cell in component['cells'].items())
    ffs={name:cell for name,cell in component['cells'].items() if cell['type']=='$aldff'}
    assert len(ffs)==62 and sum(len(cell['connections']['Q']) for cell in ffs.values())==341
    for name,port in component['ports'].items():
        if name.startswith(('count_','tag_')):continue
        assert port['bits']==original['netnames'][prefix+name]['bits']
    assert sum(len(p['bits']) for p in component['ports'].values() if p['direction']=='input')==30


def test_rd_premises_are_exact_existing_native_fields(evidence):
    record,native,_=evidence
    domain=read(BUILD/'rd_domain_symbolic_v5/summary.json')
    projected=read(BUILD/'rd_domain_symbolic_v5/data_path.json')['modules']['InstructionDataPath']
    original=native['modules']['datapath'];prefix=record['native_component_audit']['prefix']
    assert domain['output_field_values']==[0,5,8,9,10,11,18]
    assert projected['ports']['state_word_2']['bits']==original['netnames'][prefix+'issue_rd_idx_i']['bits']
    assert projected['ports']['state_word_0']['bits']==projected['ports']['decoder_word']['bits']==original['netnames'][prefix+'comm_rd_idx_i']['bits']
    assert len(domain['projection']['state_words'])==40
    for word in domain['projection']['state_words']:
        assert [original['cells'][word['cell']]['connections']['Q'][i] for i in word['original_indices']]==word['bits']


def test_exactly_275_reset_bits_and_50_cells_change(evidence):
    record,reference,query=evidence;old=reference['modules']['datapath'];new=query['modules']['datapath']
    declared=record['reset_substitution'];changes={int(b):v for b,v in declared['constant_substitutions'].items()}
    assert len(changes)==275 and set(changes.values())=={'0'}
    removed=set(old['cells'])-set(new['cells'])
    assert len(removed)==50 and removed==set(declared['deleted_ff_cells'])
    assert not set(new['cells'])-set(old['cells'])
    actual={b for name in removed for b in old['cells'][name]['connections']['Q']}
    assert actual==set(changes)
    for name in removed:
        cell=old['cells'][name];con=cell['connections'];par=cell['parameters']
        assert cell['type']=='$aldff' and con['AD']==['0']*len(con['Q'])
        assert con['CLK']==old['ports']['clk_i']['bits'] and con['ALOAD']==old['ports']['rst_ni']['bits']
        assert int(par['CLK_POLARITY'],2)==1 and int(par['ALOAD_POLARITY'],2)==0
    for name,cell in new['cells'].items():
        original=old['cells'][name]
        assert {k:v for k,v in cell.items() if k!='connections'}=={k:v for k,v in original.items() if k!='connections'}
        assert cell['connections']=={pin:[changes.get(b,b) for b in bits] for pin,bits in original['connections'].items()}
    for family in ['ports','netnames']:
        assert set(new[family])==set(old[family])
        for name,net in new[family].items():
            original=old[family][name]
            assert {k:v for k,v in net.items() if k!='bits'}=={k:v for k,v in original.items() if k!='bits'}
            assert net['bits']==[changes.get(b,b) for b in original['bits']]
    assert all(new['ports'][n]==p for n,p in old['ports'].items() if p['direction']=='input')
    assert {k:v for k,v in old.items() if k not in ['cells','ports','netnames']}=={k:v for k,v in new.items() if k not in ['cells','ports','netnames']}


def test_proof_and_negative_controls_are_bound_to_the_exact_models(evidence):
    record,_,_=evidence
    for name,result in record['local_proofs'].items():
        directory=RUN/name
        assert sha(directory/'harness.sv')==result['harness_sha256']
        assert sha(directory/'model.smt2')==result['model_sha256']
        assert sha(directory/'lowered.json')==result['lowered_sha256']
        lowered=read(directory/'lowered.json')['modules']['RegisterStatusProof']
        assert sum(c['type']=='$assert' for c in lowered['cells'].values())==50
        assert not any(b in ('x','z') for c in lowered['cells'].values() for bits in c['connections'].values() for b in bits)
        base=(directory/'base.log').read_text();assert sha(directory/'base.log')==result['base']['log_sha256']
        if name=='positive':
            assert result['base']['returncode']==0 and not result['base']['timeout'] and 'Status: PASSED' in base
            induction=(directory/'induction.log').read_text()
            assert sha(directory/'induction.log')==result['induction']['log_sha256']
            assert result['induction']['returncode']==0 and not result['induction']['timeout']
            assert 'Temporal induction successful.' in induction and 'Status: PASSED' in induction
        else:
            assert result['base']['returncode']==1 and not result['base']['timeout'] and 'Status: FAILED' in base
            assert sha(directory/'counterexample.vcd')==result['counterexample_sha256']


def test_both_certificate_replays_match_frozen_certificates(evidence):
    record,_,_=evidence
    isa=Path(__file__).resolve().parents[2]/'experiments/bounded_dynamic/len5/isa_baseline'
    cert=read(isa/'results/program_registers_certificate_v2.json')
    parent=read(Path(cert['decoder_certificate']))
    assert read(RUN/'decoder_certificate.json')==parent
    assert read(RUN/'register_certificate.json')==cert
    assert sha(RUN/'rd_export_replay/model.smt2')==sha(BUILD/'rd_domain_symbolic_v5/model.smt2')
    assert read(RUN/'rd_export_replay/lowered.json')==read(BUILD/'rd_domain_symbolic_v5/lowered.json')


def test_current_decoder_plus_inactive_query_has_a_distinct_exact_transport(evidence):
    import copy
    record,native,_=evidence
    prepared=BUILD/'harvard_rom_inactive_fu_native_prepare_v1';summary=read(prepared/'summary.json')
    original=read(prepared/'source.json')['modules']['datapath']
    current=read(prepared/'inactive_query_core.json')['modules']['datapath']
    assert sha(prepared/'inactive_query_core.json')==summary['query_core_sha256']
    assert sha(prepared/'source.json')==summary['source_json_sha256']
    assert sha(prepared/'inactive_query_core.json')!=record['query_model_sha256']
    assert summary['external_rom_domain_import']['status']=='exact_external_rom_domain_certified'
    inactive=summary['inactive_fu_import']
    assert inactive['status']=='inactive_fu_reset_facts_replayed' and inactive['assumptions_added']==0
    for path,expected in inactive['proof_dependencies_sha256'].items():assert sha(Path(path))==expected
    assert all(current['cells'][n]==original['cells'][n]==native['modules']['datapath']['cells'][n]
        for n in record['native_component_audit']['native_component_cells'])
    substitutions={int(k):v for k,v in inactive['reset_substitutions'].items()}
    selected={int(k) for k in record['reset_substitution']['constant_substitutions']}
    assert not selected&set(substitutions)
    domain=read(BUILD/'rd_domain_symbolic_v5/summary.json')['projection']
    assert not set(substitutions)&{b for word in domain['state_words'] for b in word['bits']}
    protected=set(domain['original_cell_slices'])|set(domain['retained_spill_write_control_cells'])
    for name in protected:
        transformed=copy.deepcopy(original['cells'][name])
        for pin,bits in transformed['connections'].items():
            transformed['connections'][pin]=[substitutions.get(b,b) for b in bits]
        assert current['cells'][name]==transformed
    for n in ['clk_i','rst_ni','u_backend.u_int_regstat.issue_rd_idx_i','u_backend.u_int_regstat.comm_rd_idx_i']:
        assert current['netnames'][n]['bits']==original['netnames'][n]['bits']
    # This audit establishes composition eligibility, not a rewritten current graph.
