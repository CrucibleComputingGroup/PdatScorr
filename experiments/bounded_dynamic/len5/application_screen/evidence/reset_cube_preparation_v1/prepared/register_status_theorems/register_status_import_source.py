"""Compose closed native RD domains and register-status facts in proof queries.

The source theorem is replayed on original native RTL. Its conclusions then
transfer through the already-checked decoder and inactive-FU substitutions.
No RF candidate is substituted into this query.
"""
from __future__ import annotations
import copy
import json
from pathlib import Path

from collect_register_status import audit_run
from domain_lemmas import replay_domain_export
from odc.temporal import checked_yosys,digest,formal_lower_command,formal_prepare_command,yosys_path
from register_status_lemmas import (PREFIX,check_dependencies,native_component,read,
    replay_rd_chain,require,reset_substitution)


def verify_dependencies(record): check_dependencies(record['proof_dependencies_sha256'])


def fresh_rd_predicates(design,fields,values):
    """Encode the40 proved field conclusions without reusing any existing bit ID."""
    result=copy.deepcopy(design);module=result['modules']['datapath']
    bits=[b for c in module['cells'].values() for bs in c['connections'].values() for b in bs if type(b) is int]
    bits += [b for n in [*module['ports'].values(),*module['netnames'].values()] for b in n['bits'] if type(b) is int]
    next_bit=max(bits)+1;initial=next_bit;added=[]
    require(len(fields)==40 and len({tuple(f['bits']) for f in fields})==40,'Expected40 unique original fields')
    for i,field in enumerate(fields):
        require(len(field['bits'])==5,'Expected native5-bit destination fields')
        terms=[]
        for j,value in enumerate(values):
            require(type(value) is int and 0<=value<32,'Invalid destination-field value')
            name=f'$pscorr_rd_lemma_{i}_value_{j}'
            require(name not in module['cells'],'RD predicate name collision')
            out=next_bit;next_bit+=1;terms.append(out)
            module['cells'][name]={'hide_name':1,'type':'$eq','parameters':{'A_WIDTH':5,'B_WIDTH':5,'Y_WIDTH':1,'A_SIGNED':0,'B_SIGNED':0},
                'attributes':{},'port_directions':{'A':'input','B':'input','Y':'output'},
                'connections':{'A':list(field['bits']),'B':list(format(value,'05b')[::-1]),'Y':[out]}}
            added.append(name)
        name=f'$pscorr_rd_lemma_{i}_or';require(name not in module['cells'],'RD predicate name collision')
        out=next_bit;next_bit+=1
        module['cells'][name]={'hide_name':1,'type':'$reduce_or','parameters':{'A_WIDTH':len(terms),'Y_WIDTH':1,'A_SIGNED':0},
            'attributes':{},'port_directions':{'A':'input','Y':'output'},'connections':{'A':terms,'Y':[out]}}
        added.append(name);name=f'$pscorr_rd_lemma_{i}_assume';require(name not in module['cells'],'RD predicate name collision')
        module['cells'][name]={'hide_name':1,'type':'$assume','parameters':{},
            'attributes':{'pscorr_proved_rd_field':field['cell']},'port_directions':{'A':'input','EN':'input'},
            'connections':{'A':[out],'EN':['1']}}
        added.append(name)
    return result,{'added_cells':added,'added_assumptions':40,'fresh_bit_min':initial,'fresh_bit_max':next_bit-1}


def compose_query(original,decoder,reduced,current,word_import,inactive_import,local):
    """Check exact component transport, then apply only proved constants/facts."""
    source=original['modules']['datapath'];target=reduced['modules']['datapath']
    # Reconstruct the current query from the already-audited inactive graph,
    # observation aliases, and unchanged seven-word predicate cells.
    expected=copy.deepcopy(reduced);em=expected['modules']['datapath']
    for alias,name in (('probe_insert','insert'),('probe_index','new_idx')):
        require(alias not in em['ports'],'Unexpected pre-existing observation alias')
        em['ports'][alias]={'direction':'output','bits':list(em['netnames']['u_backend.u_exec_stage.u_alu_unit.u_arith_rs.'+name]['bits'])}
    current_cells=current['modules']['datapath']['cells']
    for name in word_import['added_cells']:
        require(name not in em['cells'],'Native/word predicate collision')
        em['cells'][name]=copy.deepcopy(current_cells[name])
    require(expected==current,'Current graph differs from closed inactive substitution plus original word lemmas')
    audit=local['native_component_audit'];component,_=native_component(original,local['rd_theorem_chain']['rd_values'])
    for name,cell in component['modules']['NativeRegisterStatus']['cells'].items():
        require(decoder['modules']['datapath']['cells'].get(name)==cell==target['cells'].get(name),
                'Native register-status component changed before fact import')
    for name,port in component['modules']['NativeRegisterStatus']['ports'].items():
        if name.startswith(('count_','tag_')):continue
        require(source['netnames'][PREFIX+name]['bits']==target['netnames'][PREFIX+name]['bits'],
                'Native register-status interface aliases changed')
    fields=local['rd_theorem_chain']['unique_stored_field_lemmas']
    rd_bits={b for field in fields for b in field['bits']}
    inactive_bits={int(b) for b in inactive_import['reset_substitutions']}
    reset_bits={int(b) for b in local['reset_substitution']['constant_substitutions']}
    require(not rd_bits&(inactive_bits|reset_bits) and not inactive_bits&reset_bits,'Proved state facts overlap native RD fields')
    for field in fields:
        name=field['cell'];indices=field['original_indices']
        require([source['cells'][name]['connections']['Q'][i] for i in indices]==field['bits'],
                'Original RD visible-field binding changed')
        require([target['cells'][name]['connections']['Q'][i] for i in indices]==field['bits'],
                'Inactive substitution changed a visible RD field')
    result,patch=reset_substitution(current,audit)
    require(json.loads(json.dumps(patch))==local['reset_substitution'],'Transported reset patch differs')
    result,encoding=fresh_rd_predicates(result,fields,local['rd_theorem_chain']['rd_values'])
    for name in word_import['added_cells']:
        require(result['modules']['datapath']['cells'][name]==current_cells[name],'Original word lemma changed')
    counts={k:sum(c['type']=='$'+k for c in result['modules']['datapath']['cells'].values()) for k in ('assert','assume','cover')}
    require(counts=={'assert':0,'assume':47,'cover':0},'Expected7word+40RD derived assumptions only')
    protected=local['rd_theorem_chain']['preserved_native_projection_cells']
    touched=[name for name in protected if source['cells'][name]!=target['cells'].get(name)]
    return result,{'reset_substitution':patch,'rd_encoding':encoding,'proof_only_property_counts':counts,
        'native_component_cells_identical':len(audit['native_component_cells']),
        'original_rd_projection_cells_changed_by_preceding_closed_rewrites':touched,
        'all_visible_rd_field_bits_preserved':True,'existing_word_predicate_cells_preserved':list(word_import['added_cells'])}


def replay_local_export(run,out,yosys):
    """Reproduce the exact local50-assertion proof model without solving again."""
    out.mkdir();old=run/'positive'
    expected=f'read_json {yosys_path(run/"component.json")}\nsetundef -anyseq\nbwmuxmap\nbmuxmap\ndemuxmap\nsetundef -anyseq\n'
    expected+=f'read_verilog -formal -sv {yosys_path(old/"harness.sv")}\n'+formal_prepare_command('RegisterStatusProof')
    expected+=formal_lower_command(yosys)+'async2sync\ndffunmap\nsetundef -anyseq\ncheck -assert\n'
    expected+=f'write_json {yosys_path(old/"lowered.json")}\nwrite_smt2 -wires {yosys_path(old/"model.smt2")}\n'
    require((old/'export.ys').read_text()==expected,'Local proof export pipeline changed')
    fresh=expected.replace(yosys_path(old/'lowered.json'),yosys_path(out/'lowered.json')).replace(yosys_path(old/'model.smt2'),yosys_path(out/'model.smt2'))
    execution=checked_yosys(yosys,fresh,out,'regenerate',30)
    require(read(old/'lowered.json')==read(out/'lowered.json') and digest(old/'model.smt2')==digest(out/'model.smt2'),
            'Replayed local proof model differs')
    return execution


def import_register_status(run,original,decoder,reduced,current,word_import,inactive_import,rom_import,out,*,yosys):
    run,out=Path(run).resolve(),Path(out).resolve();out.mkdir()
    require(word_import['status']=='seven_proved_native_word_domains_imported'
        and inactive_import['status']=='inactive_fu_reset_facts_replayed'
        and rom_import['status']=='exact_external_rom_domain_certified','Closed preceding proof chain required')
    local,graph_audit=audit_run(run)
    dependencies=dict(local['source_dependencies_sha256'])
    for record in (word_import,inactive_import,rom_import):
        for path,expected in record['proof_dependencies_sha256'].items():
            require(path not in dependencies or dependencies[path]==expected,'Conflicting transitive proof dependency')
            dependencies[path]=expected
    for path in run.rglob('*'):
        if path.is_file():dependencies[str(path)]=digest(path)
    for path in (Path(__file__),Path(audit_run.__code__.co_filename),Path(replay_rd_chain.__code__.co_filename)):
        dependencies[str(path.resolve())]=digest(path)
    check_dependencies(dependencies)
    # Recover certificate-bound artifacts from the frozen local source closure.
    def sole(suffix):
        matches=[Path(p) for p in local['source_dependencies_sha256'] if p.endswith(suffix)]
        require(len(matches)==1,'Ambiguous historical proof artifact: '+suffix)
        return matches[0]
    certificate_path=sole('/isa_baseline/results/program_registers_certificate_v2.json')
    certificate=read(certificate_path);parent=read(Path(certificate['decoder_certificate']))
    require(original==read(Path(certificate['native_original_json'])),'RD replay source is not exact original native graph')
    require(decoder==read(Path(parent['native_candidate_json'])),'Query must retain the exact decoder-only native candidate')
    # Replay on ORIGINAL source before applying any new query substitution.
    _,_,chain=replay_rd_chain(certificate_path,sole('/rd_domain_symbolic_v5/summary.json').parent,
        sole('/register_baseline_prepare_v1/decoder.json'),sole('/register_baseline_prepare_v2/manifest.json').parent,
        sole('/register_pair_symbolic_v1/summary.json').parent,sole('/register_lowering_symbolic_v2/summary.json').parent,out,yosys)
    for key in ('index_bindings','rd_values','unique_stored_field_lemmas','preserved_native_projection_cells','external_premises'):
        require(chain[key]==local['rd_theorem_chain'][key],'Replayed RD theorem binding differs')
    local_export=replay_local_export(run,out/'local_export_replay',yosys)
    result,composition=compose_query(original,decoder,reduced,current,word_import,inactive_import,local)
    check_dependencies(dependencies)
    record={'status':'forty_rd_domains_and_register_status_facts_imported','query_only':True,'accepted_optimization':False,
        'new_environmental_premises':[],'new_unproved_internal_premises':0,'derived_assumptions_added':40,
        'proved_reset_bits_substituted':275,'native_hardware_export_unchanged':True,'rf_candidate_substituted':False,
        'native_rd_source_replayed_before_new_rewrites':True,'local_model_export_replay':local_export,
        'local_run':str(run),'local_summary_sha256':digest(run/'summary.json'),'local_graph_audit':graph_audit,
        'composition':composition,'proof_dependencies_sha256':dependencies,
        'transport':'Original native RD proof is replayed, then its visible-field conclusions transfer through the '
            'already-certified decoder outside-state equivalence and exact inactive-FU pointwise reset substitution. '
            'The complete register-status component is byte-identical in this target. Its local reset theorem therefore '
            'justifies275further constant substitutions. Existing word predicates remain identical. No RF candidate is imported.'}
    (out/'register_status_import_source.py').write_bytes(Path(__file__).read_bytes())
    (out/'summary.json').write_text(json.dumps(record,indent=2)+'\n')
    return result,record
