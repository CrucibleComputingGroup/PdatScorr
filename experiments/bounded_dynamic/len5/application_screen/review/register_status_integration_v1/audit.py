#!/usr/bin/env python3
"""Independent graph reconstruction of the frozen RD/register-status import.

Read-only source validation and JSON reconstruction; no tool export or solver.
"""
import copy
import hashlib
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
APP=HERE.parents[1]
ROOT=APP.parents[3]
sys.path[:0]=[str(ROOT),str(APP)]
from register_status_prepared import validate_register_status_prepared

BUILD=Path('/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build')
PREPARED=BUILD/'harvard_rom_register_status_native_prepare_v1'


def read(path):return json.loads(Path(path).read_text())
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def reconstruct(directory=PREPARED):
    before=validate_register_status_prepared(directory)
    assert sha(APP/'formal_screen.py')==sha(directory/'formal_screen.py')
    olddir=BUILD/'harvard_rom_inactive_fu_native_prepare_v1'
    localdir=BUILD/'register_status_lemmas_v2'
    source=read(directory/'source.json')['modules']['datapath']
    previous=read(directory/'inactive_query_core.json')
    target=read(directory/'register_status_query_core.json')
    assert sha(directory/'inactive_query_core.json')==sha(olddir/'inactive_query_core.json')
    assert sha(directory/'core.json')==sha(olddir/'core.json')
    assert sha(directory/'core.v')==sha(olddir/'core.v')
    assert sha(directory/'AdmissionScreen.sv')==sha(olddir/'AdmissionScreen.sv')
    assert sha(directory/'source.json')==sha(olddir/'source.json')
    domain=read(BUILD/'rd_domain_symbolic_v5/summary.json')
    fields=domain['projection']['state_words'];values=domain['output_field_values']
    assert len(fields)==40 and len({tuple(f['bits']) for f in fields})==40
    assert values==[0,5,8,9,10,11,18]
    local=read(localdir/'summary.json');composition=before['register_status_import']['composition']
    assert fields==local['rd_theorem_chain']['unique_stored_field_lemmas']
    assert composition['reset_substitution']==local['reset_substitution']
    changes={int(k):v for k,v in local['reset_substitution']['constant_substitutions'].items()}
    removed=set(local['reset_substitution']['deleted_ff_cells'])
    assert len(changes)==275 and len(removed)==50 and set(changes.values())=={'0'}
    original=previous['modules']['datapath']
    for name in local['native_component_audit']['native_component_cells']:
        assert original['cells'][name]==source['cells'][name]
    assert len(local['native_component_audit']['native_component_cells'])==506
    for f in fields:
        assert [source['cells'][f['cell']]['connections']['Q'][i] for i in f['original_indices']]==f['bits']
        assert [original['cells'][f['cell']]['connections']['Q'][i] for i in f['original_indices']]==f['bits']
    # Reconstruct the predecessor's ten changed RD-control primitives from the
    # closed inactive constant map, rather than treating them as new premises.
    inactive={int(k):v for k,v in before['inactive_fu_import']['reset_substitutions'].items()}
    protected=set(domain['projection']['original_cell_slices'])|set(domain['projection']['retained_spill_write_control_cells'])
    touched=[]
    for name in sorted(protected):
        expected=copy.deepcopy(source['cells'][name])
        for pin,bits in expected['connections'].items():expected['connections'][pin]=[inactive.get(b,b) for b in bits]
        assert original['cells'][name]==expected
        if source['cells'][name]!=expected:touched.append(name)
    assert set(touched)==set(composition['original_rd_projection_cells_changed_by_preceding_closed_rewrites']) and len(touched)==10
    assert not set(changes)&set(inactive)
    assert not {b for f in fields for b in f['bits']}&(set(changes)|set(inactive))
    # Independent whole-graph delta reconstruction. Do not call owner rewrite.
    expected=copy.deepcopy(previous);m=expected['modules']['datapath']
    actual_q=set()
    for name in removed:
        c=m['cells'].pop(name);assert c['type']=='$aldff'
        assert c['connections']['AD']==['0']*len(c['connections']['Q'])
        actual_q.update(c['connections']['Q'])
    assert actual_q==set(changes)
    for cell in m['cells'].values():
        for pin,bits in cell['connections'].items():cell['connections'][pin]=[changes.get(b,b) for b in bits]
    for kind in ['ports','netnames']:
        for net in m[kind].values():net['bits']=[changes.get(b,b) for b in net['bits']]
    used={b for c in m['cells'].values() for bs in c['connections'].values() for b in bs if type(b)is int}
    used|={b for n in [*m['ports'].values(),*m['netnames'].values()] for b in n['bits'] if type(b)is int}
    nextbit=max(used)+1;first=nextbit;added=[]
    for i,field in enumerate(fields):
        eqs=[]
        for j,value in enumerate(values):
            name=f'$pscorr_rd_lemma_{i}_value_{j}';assert name not in m['cells'];out=nextbit;nextbit+=1;eqs.append(out)
            m['cells'][name]={'hide_name':1,'type':'$eq','parameters':{'A_WIDTH':5,'B_WIDTH':5,'Y_WIDTH':1,'A_SIGNED':0,'B_SIGNED':0},
                'attributes':{},'port_directions':{'A':'input','B':'input','Y':'output'},
                'connections':{'A':field['bits'],'B':[str((value>>k)&1) for k in range(5)],'Y':[out]}}
            added.append(name)
        name=f'$pscorr_rd_lemma_{i}_or';assert name not in m['cells'];out=nextbit;nextbit+=1
        m['cells'][name]={'hide_name':1,'type':'$reduce_or','parameters':{'A_WIDTH':7,'Y_WIDTH':1,'A_SIGNED':0},
            'attributes':{},'port_directions':{'A':'input','Y':'output'},'connections':{'A':eqs,'Y':[out]}}
        added.append(name);name=f'$pscorr_rd_lemma_{i}_assume';assert name not in m['cells']
        m['cells'][name]={'hide_name':1,'type':'$assume','parameters':{},'attributes':{'pscorr_proved_rd_field':field['cell']},
            'port_directions':{'A':'input','EN':'input'},'connections':{'A':[out],'EN':['1']}}
        added.append(name)
    assert expected==target
    assert len(added)==360 and nextbit-first==320 and not set(range(first,nextbit))&used
    assert composition['rd_encoding']=={'added_cells':added,'added_assumptions':40,'fresh_bit_min':first,'fresh_bit_max':nextbit-1}
    wordcells=before['native_word_domain_import']['added_cells']
    assert len(wordcells)==119 and set(wordcells).isdisjoint(added)
    assert all(m['cells'][name]==original['cells'][name] for name in wordcells)
    assert all(m['ports'][name]==port for name,port in original['ports'].items())
    assert {k:sum(c['type']=='$'+k for c in m['cells'].values()) for k in ['assert','assume','cover']}=={'assert':0,'assume':47,'cover':0}
    # The archived local replays occur on original source, not on changed controls.
    replay=directory/'register_status_theorems'
    assert read(replay/'decoder_certificate.json')==read(localdir/'decoder_certificate.json')
    assert read(replay/'register_certificate.json')==read(localdir/'register_certificate.json')
    for subdir,source_dir in [('rd_export_replay',BUILD/'rd_domain_symbolic_v5'),('local_export_replay',localdir/'positive')]:
        assert sha(replay/subdir/'model.smt2')==sha(source_dir/'model.smt2')
        assert read(replay/subdir/'lowered.json')==read(source_dir/'lowered.json')
    after=validate_register_status_prepared(directory);assert before==after
    return {'record':before,'fields':fields,'values':values,'added':added,'new_bit_range':[first,nextbit-1],
        'touched_RD_control_cells':touched,'exact_graph_reconstruction':True,
        'domain_dependencies_verified_before_and_after':True}


def main():
    result=reconstruct();record=result.pop('record')
    files=[Path(__file__),ROOT/'tests/unit/test_register_status_integration_review.py',
        APP/'register_status_import.py',APP/'register_status_prepared.py',APP/'formal_screen.py',
        PREPARED/'summary.json',PREPARED/'source.json',PREPARED/'core.json',PREPARED/'core.v',
        PREPARED/'AdmissionScreen.sv',PREPARED/'inactive_query_core.json',PREPARED/'register_status_query_core.json',
        PREPARED/'screen.json',PREPARED/'screen.aig',PREPARED/'prepare.ys',PREPARED/'prepare.log',PREPARED/'export.ys',PREPARED/'export.log']
    files += [p for p in (PREPARED/'register_status_theorems').rglob('*') if p.is_file()]
    report={'status':'independent_register_status_integration_review_passed','solver_invoked':False,'accepted_optimization':False,
        'source_sha256':{str(p):sha(p) for p in files},'prepared_directory':str(PREPARED),
        'native_core_json_sha256':record['core_json_sha256'],'harness_sha256':record['harness_sha256'],
        'previous_query_sha256':sha(PREPARED/'inactive_query_core.json'),'new_query_sha256':record['query_core_sha256'],
        'input_graph_reconstructed_from_prior_same_source_family':True,'rf_candidate_used_as_query':False,
        'source_RD_theorem_replayed_before_closed_inactive_constant_changes':True,
        'all_506_regstat_cells_exact_original_before_substitution':True,'substituted_reset_bits':275,
        'added_exact_RD_membership_predicate_cells':360,'added_fresh_predicate_bits':320,'derived_assumptions_added':40,
        'visible_RD_fields':40,'visible_RD_bits':200,'unchanged_existing_word_predicate_cells':119,
        'query_properties':{'assert':0,'assume':47,'cover':0},'lowered_properties':record['query_property_counts'],
        'source_dependency_count':len(record['native_word_domain_import']['proof_dependencies_sha256']),
        'aig_header':record['aig_header'],'native_arithmetic':record['abstraction_mode'],
        'prepare_only_enforced':True,'data':result,
        'limitations':['Preparation/lemma-composition audit only; no main ALU-admission verdict or hardware rewrite is accepted.',
        '40additional assumptions are previously proved native visible RD conclusions. Their original external ROM/domain/initial-reset dependencies remain required.',
        'The public composition helper expects the reduced graph supplied by the verified inactive importer; this frozen formal_screen call chain supplies it directly. A future reusable standalone importer should bind that argument explicitly to the inactive record hash.',
        'AIG counts are formal encoding sizes, not physical area.']}
    (HERE/'review.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':report['status'],'dependencies':report['source_dependency_count'],'query_sha256':report['new_query_sha256'],'artifacts':len(files)}))


if __name__=='__main__':main()
