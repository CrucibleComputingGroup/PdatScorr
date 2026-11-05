#!/usr/bin/env python3
"""Independently reconstruct the frozen cube delta on the48-premise query.

No exporter, solver, or hardware mutator is invoked.
"""
import copy
import hashlib
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
APP=HERE.parents[1];ROOT=APP.parents[3]
sys.path[:0]=[str(ROOT),str(APP)]
from register_status_prepared import validate_register_status_prepared
from reset_cube_prepared import validate_reset_cube_prepared

BUILD=Path('/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build')
PREPARED=BUILD/'harvard_rom_register_status_cube_native_prepare_v1'
CUBE=BUILD/'reset_cube_native_fixedpoint_v1'


def read(path):return json.loads(Path(path).read_text())
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def reconstruct(directory=PREPARED):
    record=validate_reset_cube_prepared(directory)
    assert record['status']=='prepared_query_only' and record['engine']=='prepare' and not record['accepted_optimization']
    assert record['abstraction_mode']=='none' and record['datapath_abstraction'] is None
    candidates=[v for v in record.values() if isinstance(v,dict) and v.get('status')=='closed_reset_cube_delta_imported']
    assert len(candidates)==1;cube=candidates[0]
    assert cube['assumptions_added']==0 and cube['new_unproved_internal_premises']==0 and not cube['new_environmental_premises']
    reference=Path(cube['reference_prepared_directory']);ref=validate_register_status_prepared(reference)
    assert sha(reference/'summary.json')==cube['reference_summary_sha256']
    querypath=Path(record['query_core_path']);assert querypath.parent==directory
    assert sha(querypath)==record['query_core_sha256']
    current=read(Path(ref['query_core_path']));actual=read(querypath)
    proof=read(CUBE/'summary.json');rows=read(CUBE/'selected_words.json')
    assert proof['status']=='reset_cube_certified_query_patch_only' and proof['source_sha256']==cube['cube_source_sha256']
    assert sha(CUBE/'source.json')==cube['cube_source_sha256']=='bb52d686f974809e0bebd4e2b373414ec9a53af34cff5a6a48d1e5ab2465307b'
    assert sha(CUBE/'query_only_patch.json')==cube['source_cube_patch_sha256']=='6192d7a41d51a0e11e8e4bb2b13128fc767ba7e4061cce27612ef7ee727e2323'
    review=read(Path(cube['independent_review_path']))
    assert sha(Path(cube['independent_review_path']))==cube['independent_review_sha256']
    assert review['status']=='independent_reset_cube_source_semantics_and_artifact_review_passed'
    dependencies={}
    for field in ['native_word_domain_import','external_rom_domain_import','inactive_fu_import','register_status_import']:
        for path,value in record[field]['proof_dependencies_sha256'].items():
            assert dependencies.get(path,value)==value;dependencies[path]=value
    for path,value in cube['proof_dependencies_sha256'].items():
        assert dependencies.get(path,value)==value;dependencies[path]=value
        assert record['native_word_domain_import']['proof_dependencies_sha256'].get(path)==value
    for path,value in dependencies.items():assert sha(Path(path))==value
    # Whole output graph is rebuilt without calling the owner's patch function.
    expected=copy.deepcopy(current);m=expected['modules']['datapath'];old=current['modules']['datapath']
    constants={bit:value for row in rows for bit,value in zip(row['q'],row['reset_value'])}
    assert len(rows)==42 and len(constants)==583 and set(constants.values())=={'0'}
    assert constants=={int(k):v for k,v in cube['composition']['constant_substitutions'].items()}
    for row in rows:
        assert m['cells'][row['name']]==row['cell']
        del m['cells'][row['name']]
    for cell in m['cells'].values():
        for pin,bits in cell['connections'].items():
            if cell['port_directions'][pin]=='input':cell['connections'][pin]=[constants.get(b,b) for b in bits]
            else:assert not set(bits)&set(constants)
    for group in ['ports','netnames']:
        for item in m[group].values():item['bits']=[constants.get(b,b) for b in item['bits']]
    assert expected==actual
    word=ref['native_word_domain_import']['added_cells']
    rd=ref['register_status_import']['composition']['rd_encoding']['added_cells']
    assert len(word)==119 and len(rd)==360 and not set(word)&set(rd)
    assert word+rd==cube['composition']['existing_predicate_cells_preserved']
    for name in word+rd:
        assert old['cells'][name]==m['cells'][name]
        assert not any(set(bs)&set(constants) for bs in m['cells'][name]['connections'].values())
    assert old['ports']==m['ports']
    previous_constants={int(k) for k in ref['register_status_import']['composition']['reset_substitution']['constant_substitutions']}
    inactive_constants={int(k) for k in ref['inactive_fu_import']['reset_substitutions']}
    assert len(previous_constants)==275 and len(inactive_constants)==1761
    assert not set(constants)&(previous_constants|inactive_constants)
    assert {k:sum(c['type']=='$'+k for c in m['cells'].values()) for k in ['assert','assume','cover']}=={'assert':0,'assume':47,'cover':0}
    assert record['query_property_counts']=={'assert':3,'assume':48,'cover':0}
    for name in ['core.json','core.v','AdmissionScreen.sv','source.json','program.hex']:
        assert (directory/name).read_bytes()==(reference/name).read_bytes()
    assert sha(directory/'core.json')==record['core_json_sha256']==cube['native_core_sha256']
    assert sha(directory/'AdmissionScreen.sv')==record['harness_sha256']==cube['harness_sha256']
    assert record['native_hardware_contains_formal_properties'] is False
    lower=read(directory/'screen.json')['modules']['AdmissionScreen']
    assert sha(directory/'screen.json')==record['screen_json_sha256']
    assert {k:sum(c['type']=='$'+k for c in lower['cells'].values()) for k in ['assert','assume','cover']}==record['query_property_counts']
    assert not any(b in ('x','z') for c in lower['cells'].values() for bs in c['connections'].values() for b in bs)
    header=(directory/'screen.aig').read_bytes().split(b'\n',1)[0].decode().split()
    assert header==record['aig_header'] and header[0]=='aig' and int(header[4])==0 and list(map(int,header[6:]))==[3,48,0,0]
    assert sha(directory/'screen.aig')==record['aig_sha256']
    replay_dirs={}
    for mode,item in cube['export_replays'].items():
        assert mode in ('base','induction') and item['byte_identical'] and item['solver_rerun'] is False
        executions=item['export_replays'];assert len(executions)==2
        replay=Path(executions[0]['argv'][-1]).parent.parent;replay_dirs[mode]=str(replay)
        oldproof=CUBE/('final_'+mode)
        for name in ['symbolized_before_prep.json','binary_inputs_before_prep.json','normalized_symbolic.json','lowered.json']:
            assert (replay/name).read_bytes()==(oldproof/name).read_bytes()
        assert sha(replay/'lowered.json')==item['model_sha256']==proof['final_proofs'][mode]['lowered_sha256']
        assert sha(oldproof/'sat.log')==item['original_sat_log_sha256']==proof['final_proofs'][mode]['sat_log_sha256']
        for execution in executions:
            assert execution['returncode']==0 and not execution['timeout']
            script=Path(execution['argv'][-1]);assert sha(script)==execution['script_sha256']
            assert sha(script.parent/'run.log')==execution['log_sha256']
            assert not any(line.lstrip().startswith(('sat ','tee ','abc ')) for line in script.read_text().splitlines())
    assert set(replay_dirs)=={'base','induction'}
    assert validate_register_status_prepared(reference)==ref
    assert validate_reset_cube_prepared(directory)==record
    for path,value in dependencies.items():assert sha(Path(path))==value
    return {'record':record,'cube_record':cube,'exact_graph_reconstruction':True,'reference':str(reference),
        'dependencies':dependencies,'replay_directories':replay_dirs,'word_cells':word,'RD_cells':rd,
        'combined_AIG_header':header,'previous_AIG_header':ref['aig_header'],
        'eight_CDB_arbiter_bits_removed':cube['composition']['cdb_arbitration_bits_substituted']}


def main():
    result=reconstruct();record=result.pop('record');cube=result.pop('cube_record');dependencies=result.pop('dependencies')
    files=[Path(__file__),ROOT/'tests/unit/test_reset_cube_integration_review.py',APP/'reset_cube_import.py',APP/'reset_cube_prepared.py',
        PREPARED/'formal_screen.py',PREPARED/'summary.json',PREPARED/'register_status_query_core.json',
        Path(record['query_core_path']),PREPARED/'screen.json',PREPARED/'screen.aig',PREPARED/'core.json',PREPARED/'core.v',
        PREPARED/'AdmissionScreen.sv',PREPARED/'prepare.ys',PREPARED/'prepare.log',PREPARED/'export.ys',PREPARED/'export.log']
    for directory in result['replay_directories'].values():files += [p for p in Path(directory).rglob('*') if p.is_file()]
    report={'status':'independent_reset_cube_import_and_combined_preparation_review_passed','solver_invoked':False,
        'accepted_optimization':False,'native_arithmetic':True,'native_core_json_sha256':record['core_json_sha256'],
        'harness_sha256':record['harness_sha256'],'combined_query_sha256':record['query_core_sha256'],
        'properties':record['query_property_counts'],'new_assumptions':0,'new_reset_bits':583,'prior_register_status_bits':275,
        'preserved_predicate_cells':479,'preserved_proved_assumptions':47,'dependencies_verified_before_and_after':len(dependencies),
        'source_sha256':{str(p):sha(p) for p in files},'data':result,
        'limitations':['Prepare-only composition review; no target solver outcome, hardware acceptance, or physical-area result.',
        'Original reset/domain/platform proof dependencies remain required; the new cube adds no timing or admission premise.',
        '583bits intersect8retained native GLAFFs, with no ALU-RS state; no proof-speed benefit is established by preparation alone.']}
    (HERE/'combined_review.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':report['status'],'dependencies':report['dependencies_verified_before_and_after'],
        'query_sha256':report['combined_query_sha256'],'AIG':result['combined_AIG_header']}))


if __name__=='__main__':main()
