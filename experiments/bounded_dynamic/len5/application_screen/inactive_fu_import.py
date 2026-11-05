"""Replay and compose source-bound inactive-FU reset facts for proof queries."""
from __future__ import annotations
import copy
import json
from pathlib import Path

import odc.temporal as temporal
from odc.temporal import checked_yosys, digest, formal_lower_command, formal_prepare_command, proof_passed, yosys_path
import inactive_fu_lemmas as generator
import reset_storage
from collect_inactive_fu import audit_query

HERE=Path(__file__).resolve().parent


def require(value,message):
    if not value:raise ValueError(message)


def read(path):return json.loads(Path(path).read_text())


def verify_dependencies(record):
    for path,expected in record['proof_dependencies_sha256'].items():
        require(digest(Path(path))==expected,'Inactive-FU proof dependency changed: '+path)


def check_induction(directory,positive,yosys):
    """No bounded-only verdict, altered solver flags, or different SMT model."""
    model=directory/'model.smt2'
    prefix=[str(Path(yosys).with_name('yosys-smtbmc')),'-s','z3','-t','4','--noprogress']
    for mode in ('base','induction'):
        execution=positive[mode]
        expected=prefix+(['-i'] if mode=='induction' else ['--dump-vcd',str(directory/'counterexample.vcd')])+[str(model)]
        require(execution['argv']==expected and proof_passed(execution),'Missing exact unbounded lemma obligation')
        require(digest(Path(execution['log']))==execution['log_sha256'],'Lemma solver log changed')
    require('Temporal induction successful.' in Path(positive['induction']['log']).read_text(),'Missing induction certificate outcome')


def replay_row(directory,projection,audit,out,yosys):
    positive=directory/'positive';record=read(directory/'summary.json')
    require(record['status']=='conditional_reset_storage_proved' and record['admission_during_reset_restricted'] is False,
            'Row theorem has an unsupported reset or proof scope')
    require(record['projection']==audit and read(directory/'projection.json')==projection,'Native row projection changed')
    require((positive/'harness.sv').read_text()==reset_storage.harness(projection,audit),'Row theorem premises or observation changed')
    for path,expected in record['dependencies_sha256'].items():require(digest(Path(path))==expected,'Row artifact changed')
    proof=record['proofs']['positive'];check_induction(positive,proof,yosys)
    require(proof['proven'] and digest(positive/'model.smt2')==proof['model_sha256'] and
            digest(positive/'lowered.json')==proof['lowered_sha256'],'Row theorem model digest changed')
    prefix=(f'read_json {yosys_path(directory/"projection.json")}\nsetundef -anyseq\n'
            'bwmuxmap\nbmuxmap\ndemuxmap\nsetundef -anyseq\n'+
            f'read_verilog -formal -sv {yosys_path(positive/"harness.sv")}\n'+
            formal_prepare_command('ResetStorageProof')+formal_lower_command(yosys)+
            'async2sync\ndffunmap\nsetundef -anyseq\ncheck -assert\n')
    suffix=f'write_json {yosys_path(positive/"lowered.json")}\nwrite_smt2 -wires {yosys_path(positive/"model.smt2")}\n'
    require((positive/'export.ys').read_text()==prefix+suffix,'Row export contains changed transformation or hidden premise')
    out.mkdir()
    execution=checked_yosys(yosys,prefix+f'write_json {yosys_path(out/"lowered.json")}\nwrite_smt2 -wires {yosys_path(out/"model.smt2")}\n',out,'replay',20)
    require(read(out/'lowered.json')==read(positive/'lowered.json') and digest(out/'model.smt2')==proof['model_sha256'],
            'Fresh native row JSON/SMT differs from proved model')
    module=read(out/'lowered.json')['modules']['ResetStorageProof']
    counts={kind:sum(c['type']=='$'+kind for c in module['cells'].values()) for kind in ('assert','assume','cover')}
    require(counts=={'assert':1,'assume':2,'cover':0},'Unexpected local row property set')
    require(not any(bit in ('x','z') for c in module['cells'].values() for bs in c['connections'].values() for bit in bs),
            'Undefined literal survived row proof preparation')
    return record,{'execution':execution,'properties':counts,'smt_sha256':digest(out/'model.smt2'),'solver_rerun':False}


def import_inactive_facts(run,certificate_path,native,rs_source,directory,*,yosys,dependency_records):
    """Return exact proven substitutions; the caller must close the ROM domain."""
    run=Path(run).resolve();certificate_path=Path(certificate_path).resolve();rs_source=Path(rs_source).resolve()
    directory=Path(directory).resolve();directory.mkdir()
    info=read(run/'summary.json');certificate=read(certificate_path)
    require({r.get('status') for r in dependency_records}==
            {'seven_proved_native_word_domains_imported','exact_external_rom_domain_certified'},
            'Both closed native-word and external-ROM theorem records are required')
    require(info['status']=='program_only_native_reset_facts_composed' and info['query_only'] and
            info['native_hardware_export_unchanged'] and info['accepted_hardware_optimization'] is False,
            'Inactive-FU artifact is not a closed query-only theorem composition')
    require(info['new_environmental_premises']==[] and info['timing_premises']==[] and
            info['external_premises']==certificate['external_premises'],'Inactive-FU theorem changed external premises')
    require(digest(run/'native_input.json')==info['native_input_sha256']==certificate['native_candidate_sha256'] and
            native==read(run/'native_input.json'),'Inactive-FU theorem belongs to a different native candidate')
    require(info['original_native_sha256']==certificate['native_original_sha256'],'Original native source differs')
    require(digest(run/'query_only.json')==info['query_model_sha256'],'Recorded query graph changed')
    dependencies={}
    def bind(path,expected=None):
        path=Path(path).resolve();actual=digest(path)
        require(expected is None or actual==expected,'Proof source changed before import: '+str(path))
        require(str(path) not in dependencies or dependencies[str(path)]==actual,'Conflicting dependency binding')
        dependencies[str(path)]=actual
    for record in dependency_records:
        for path,expected in record['proof_dependencies_sha256'].items():bind(path,expected)
    direct=info['source_dependency_sha256']
    for path,expected in direct.items():bind(path,expected)
    summaries=[Path(path) for path in direct if Path(path).name=='summary.json']
    eu_paths=[p.parent for p in summaries if read(p).get('status')=='native_register_and_dispatch_lemmas_proved']
    diagnostic_paths=[p.parent for p in summaries if 'candidate_unrestricted' in read(p).get('tests',{})]
    require(len(eu_paths)==len(diagnostic_paths)==1,'Missing unique native EU proof dependencies')
    eu_run,diagnostic=eu_paths[0],diagnostic_paths[0]
    require(any(Path(p).name=='arith_rs.sv' and expected==digest(rs_source) for p,expected in direct.items()),
            'RS source header differs from source-bound row proofs')
    for root in (run,eu_run,diagnostic):
        for path in root.rglob('*'):
            if path.is_file():bind(path)
    for path,expected in read(eu_run/'summary.json')['dependency_sha256'].items():bind(path,expected)
    for path,expected in read(diagnostic/'summary.json')['source_sha256'].items():bind(path,expected)
    for path in [certificate_path,rs_source,Path(__file__),Path(temporal.__file__),
                 HERE/'inactive_fu_lemmas.py',HERE/'eu_register_lemma.py',HERE/'eu_domain_diagnostic.py',
                 HERE/'reset_storage.py',HERE/'collect_inactive_fu.py']:
        bind(path)
    require(digest(HERE/'inactive_fu_lemmas.py')==digest(run/'inactive_fu_lemmas_source.py'),'Inactive theorem generator changed')
    eu_out=directory/'eu_chain';eu_out.mkdir()
    original,candidate,closed,eu,chain=generator.validate_eu_chain(eu_run,certificate_path,diagnostic,eu_out,yosys)
    require(closed==certificate and candidate==native,'Replayed closed certificate changed native input')
    check_induction(eu_run/'register',eu['proofs']['register'],yosys)
    records=[];replays={};banks={};header=rs_source.read_text()
    for bank,prefix in generator.BANKS.items():
        module=original['modules']['datapath'];depth=len(module['netnames'][prefix+'empty']['bits'])
        require(depth==4 and info['banks'][bank]['depth']==depth and info['banks'][bank]['prefix']==prefix,'Bank scope/depth changed')
        binding=generator.insertion_binding(module,prefix,eu['native_'+bank+'_issue_valid_bit'])
        require(binding==info['banks'][bank]['insertion_discharge'],'Native no-admission discharge changed')
        require(module['netnames'][prefix+'clk_i']['bits']==module['ports']['clk_i']['bits'] and
                module['netnames'][prefix+'rst_ni']['bits']==module['ports']['rst_ni']['bits'],'Bank reset premise is not native reset')
        require(candidate['modules']['datapath']['cells'][binding['cell_name']]==binding['cell'],'Decoder changed native insertion')
        require([entry['row'] for entry in info['banks'][bank]['rows']]==list(range(depth)),'Missing or duplicate row theorem')
        for row in range(depth):
            projection,audit=reset_storage.project_row(original,row,header,prefix=prefix)
            required=set(audit['combinational_cells'])|{item['cell'] for item in audit['selected_ff_slices']}
            require(all(module['cells'][name]==candidate['modules']['datapath']['cells'][name] for name in required),
                    'Certified decoder modified native row proof logic')
            raw=run/f'{bank}_row_{row}'
            require(digest(raw/'summary.json')==info['banks'][bank]['rows'][row]['local_summary_sha256'],'Local row summary changed')
            record,replay=replay_row(raw,projection,audit,directory/f'{bank}_row_{row}',yosys)
            records.append(record);replays[f'{bank}_{row}']=replay
        banks[bank]=binding
    rebuilt,patch=reset_storage.conditional_rewrite(original,records)
    require(patch==info['row_reset_substitution'],'Reconstructed native reset substitutions differ')
    replaced={int(bit) for bit in patch['constant_substitutions']}
    a,b=original['modules']['datapath'],candidate['modules']['datapath']
    changed={name for name in a['cells'] if a['cells'][name]!=b['cells'][name]}
    require(changed==set(certificate['changed_cells']),'Unexpected decoder substitution')
    for name in changed:
        require(not any(set(bits)&replaced for bits in b['cells'][name]['connections'].values()),'Decoder overlaps proved reset state')
        rebuilt['modules']['datapath']['cells'][name]=copy.deepcopy(b['cells'][name])
    path=generator.native_path(a);query=generator.substitute_visible_register_high(rebuilt,path)
    require(path['ireg_high_bit']==info['native_visible_register_high_substituted'],'Visible native EU bit differs')
    require(query==read(run/'query_only.json'),'Exact reconstructed query differs from recorded graph')
    graph=audit_query(candidate,query,info)
    require(graph['reset_bits']==1761,'Expected exactly 1761 proved reset bits')
    substitutions=dict(patch['constant_substitutions']);substitutions[str(path['ireg_high_bit'])]='0'
    record={'status':'inactive_fu_reset_facts_replayed','query_only':True,'accepted_optimization':False,
        'assumptions_added':0,'native_hardware_export_unchanged':True,'new_environmental_premises':[],
        'query_model_sha256':info['query_model_sha256'],'native_candidate_sha256':info['native_input_sha256'],
        'reset_substitutions':substitutions,'graph_audit':graph,'insertion_discharges':banks,
        'eu_replay':chain,'row_export_replays':replays,'proof_dependencies_sha256':dependencies,
        'composition':'Exact reset-state substitutions follow from the closed program-only decoder/register/dispatch/insertion chain and eight source-native row inductions. The separately validated ROM environment discharges the same external word premise. No ALU admission bound or additional timing premise is assumed.'}
    verify_dependencies(record)
    (directory/'importer_source.py').write_bytes(Path(__file__).read_bytes())
    (directory/'summary.json').write_text(json.dumps(record,indent=2)+'\n')
    return query,record
