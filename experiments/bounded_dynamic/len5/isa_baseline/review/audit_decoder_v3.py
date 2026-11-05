#!/usr/bin/env python3
"""Read-only audit of the frozen decoder certificate; launches no proof tools."""
from __future__ import annotations
import argparse
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys


def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def read(path): return json.loads(path.read_text())


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('certificate', type=Path)
    ap.add_argument('--rom-manifest', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    cert = read(args.certificate)
    original_path, candidate_path = Path(cert['native_original_json']), Path(cert['native_candidate_json'])
    source, target = read(original_path)['modules']['datapath'], read(candidate_path)['modules']['datapath']
    prepared_dir, candidate_dir = original_path.parent, candidate_path.parent
    domain_dir, pair_dir = Path(cert['domain_summary']).parent, Path(cert['paired_proof_summary']).parent
    domain, pair = read(domain_dir/'summary.json'), read(pair_dir/'summary.json')
    prepared, candidate = read(prepared_dir/'manifest.json'), read(candidate_dir/'summary.json')
    bindings = {original_path: cert['native_original_sha256'], candidate_path: cert['native_candidate_sha256'],
        domain_dir/'summary.json': cert['domain_summary_sha256'], pair_dir/'summary.json': cert['paired_proof_summary_sha256'],
        candidate_dir/'summary.json': cert['candidate_summary_sha256'],
        domain_dir/'prove_domain_source.py': cert['domain_source_snapshot_sha256'],
        domain_dir/'data_path.json': cert['domain_projection_json_sha256'],
        domain_dir/'symbolized_before_prep.json': cert['domain_symbolized_before_prep_sha256'],
        pair_dir/'temporal_source.py': cert['paired_proof_implementation_sha256'],
        prepared_dir/'decoder.json': prepared['decoder_json_sha256'],
        args.certificate.parents[1]/'certify.py': cert['certifier_sha256'],
        prepared_dir/'manifest.json': candidate['prepared_manifest_sha256'],
        domain_dir/'harness.sv': domain['harness_sha256'],
        pair_dir/'proof/miter.aig': pair['proof']['aig_sha256']}
    bindings.update({Path(p): h for p,h in cert['proof_log_sha256'].items()})
    for key in ['reference','candidate','harness']:
        p=candidate_dir/(key+('.sv' if key=='harness' else '.v'))
        bindings[p]=pair['proof'][key+'_sha256']
    for p,h in bindings.items(): assert sha(p)==h, p
    assert cert['status']=='component_equivalence_and_domain_propagation_certified'
    assert cert['external_premises']==['initial rst_ni == 0','(rst_ni && instr_rvalid_i) -> instruction response word in declared domain']
    assert domain['external_word_premise_guard']=='rst_ni && instr_rvalid_i'
    assert 'if (rst_ni && response_valid) assume(' in (domain_dir/'harness.sv').read_text()
    domain_harness=(domain_dir/'harness.sv').read_text()
    assert f'if (rst_ni && response_valid) assume({cert["domain_expression"]});' in domain_harness
    assert domain_harness.count('assume(')==2 and domain_harness.count('assert(')==7
    for phase in ['base','induction']:
        run=domain[phase];log=Path(run['log']).read_text()
        assert run['returncode']==0 and not run['timeout']
        assert re.findall(r'Status:\s*(\w+)',log)==['PASSED']
    assert pair['status']=='proved' and pair['proof']['proven']
    assert pair['proof']['property_counts']=={'assert':13,'assume':1,'cover':0}
    assert pair['proof']['initial_state']['paired_state_bits']==0
    pair_model=read(pair_dir/'proof/miter.json')['modules']['TemporalMiter']
    assert {kind:sum(c['type']=='$'+kind for c in pair_model['cells'].values()) for kind in ['assert','assume']}=={'assert':13,'assume':1}
    with (pair_dir/'proof/miter.aig').open('rb') as f: aig_header=f.readline().decode().split()
    assert aig_header[0]=='aig' and int(aig_header[4])==0 and int(aig_header[6])==13 and int(aig_header[7])==1
    pdr=pair['proof']['pdr'];log=Path(pdr['log']).read_text()
    assert pdr['returncode']==0 and not pdr['timeout']
    assert len(re.findall(r'(?m)^Property proved\.',log))==1
    assert not re.search(r'\b(error|failed|undecided|disproved|timed out|time limit|was asserted)\b',log,re.I)
    assert source['ports']==target['ports'] and source['netnames']==target['netnames']
    assert source['cells'].keys()==target['cells'].keys()
    changed={n for n in source['cells'] if source['cells'][n]!=target['cells'][n]}
    assert changed==set(cert['changed_cells'])=={x['cell'] for x in candidate['accepted']}
    decoder=read(prepared_dir/'decoder.json')['modules']['DecoderBase']
    reference_component=read(candidate_dir/'reference.json')['modules']['DecoderBase']
    candidate_component=read(candidate_dir/'candidate.json')['modules']['DecoderBase']
    assert reference_component==decoder
    assert reference_component['ports']==candidate_component['ports']
    assert changed<=decoder['cells'].keys()
    for n,c in decoder['cells'].items():
        assert c==source['cells'][n]
        assert candidate_component['cells'][n]==target['cells'][n]
        assert not any(x in c['type'].lower() for x in ('ff','mem','latch'))
    assert not any(c['type'] in ('$anyseq','$anyconst','$assert','$assume','$check','$cover') for c in target['cells'].values())
    observed={b for p in decoder['ports'].values() if p['direction']=='output' for b in p['bits']}
    component_drivers={b for c in decoder['cells'].values() for p,d in c['port_directions'].items() if d=='output' for b in c['connections'][p] if isinstance(b,int)}
    leaks=[]
    for n,c in source['cells'].items():
        if n in decoder['cells']: continue
        for p,d in c['port_directions'].items():
            if d=='input':
                for b in set(c['connections'][p])&component_drivers-observed: leaks.append((n,p,b))
    for n,p in source['ports'].items():
        if p['direction']=='output':
            leaks += [('top',n,b) for b in set(p['bits'])&component_drivers-observed]
    assert not leaks
    projected=read(domain_dir/'data_path.json')['modules']['InstructionDataPath']
    # Rebuild the exact source-bound projection with its frozen reviewed method.
    code_root=Path(__file__).resolve().parents[5]
    len5=Path(__file__).resolve().parents[2]
    sys.path[:0]=[str(code_root),str(len5),str(len5/'isa_baseline')]
    spec=importlib.util.spec_from_file_location('reviewed_domain',domain_dir/'prove_domain_source.py')
    method=importlib.util.module_from_spec(spec);spec.loader.exec_module(method)
    rebuilt,audit=method.data_projection({'modules':{'datapath':source}})
    assert rebuilt['modules']['InstructionDataPath']==projected and audit==domain['projection']
    retained=set(audit['original_cell_slices'])|set(audit['retained_spill_write_control_cells'])
    assert not changed&retained
    for n in audit['retained_spill_write_control_cells']:assert projected['cells'][n]==source['cells'][n]
    drivers={b:(n,c,p) for n,c in source['cells'].items() for p,d in c['port_directions'].items() if d=='output' for b in c['connections'][p] if isinstance(b,int)}
    assert all(drivers[b][1]['type']=='$aldff' and drivers[b][2]=='Q' for b in audit['arbitrary_control_bits'])
    assert audit['internal_assumptions_added']==0 and len(audit['state_words'])==6
    symbolized=read(domain_dir/'symbolized_before_prep.json')['modules']['InstructionDataPath']
    lowered=read(domain_dir/'lowered.json')['modules']['DomainProof']
    for m in [symbolized,lowered]:
        assert not any(b in ('x','z') for c in m['cells'].values() for bits in c['connections'].values() for b in bits)
    n_any=sum(len(c['connections']['Y']) for c in symbolized['cells'].values() if c['type']=='$anyseq')
    assert n_any==194==domain['symbolic_undefined_bits_before_prep']
    counts={kind:sum(c['type']=='$'+kind for c in lowered['cells'].values()) for kind in ['assert','assume']}
    assert counts=={'assert':7,'assume':2}
    export=(domain_dir/'export.ys').read_text()
    assert export.index('setundef -anyseq')<export.index('prep -top')
    prepare=(pair_dir/'proof/prepare.ys').read_text()
    assert prepare.index('setundef -anyseq')<prepare.index('proc -norom -noopt')<prepare.index('prep -top')
    assert '-init' not in prepare and '-params' not in prepare
    harness=(candidate_dir/'harness.sv').read_text()
    outputs={n:len(p['bits']) for n,p in decoder['ports'].items() if p['direction']=='output'}
    assert outputs==cert['decoder_outputs'] and len(outputs)==13
    for n in outputs:assert harness.count(f'assert(a_{n} == b_{n});')==1
    assert harness.count('assume(')==1 and f'assume({cert["domain_expression"]});' in harness
    alphabet={int(w,16) for w in re.findall(r"instruction_i == 32'h([0-9a-f]+)",cert['domain_expression'])}|{0}
    rom=read(args.rom_manifest)
    assert alphabet=={int(x['word'],16) for x in rom['instruction_words']}|{0}
    result={'status':'reviewed_for_reset_conditioned_compositional_import','certificate_sha256':sha(args.certificate),
        'native_original_sha256':sha(original_path),'native_candidate_sha256':sha(candidate_path),
        'corrected_initial_premise':'rst_ni && instr_rvalid_i -> 14 ELF instruction words or zero; initial reset; arbitrary payload during reset',
        'decoder_output_ports':outputs,'decoder_changes':len(changed),'external_consumer_leaks':leaks,
        'retained_domain_data_cells':len(audit['original_cell_slices']),'retained_domain_control_cells':len(audit['retained_spill_write_control_cells']),
        'native_instruction_state_words':6,'arbitrary_control_ff_q_bits':len(audit['arbitrary_control_bits']),
        'preoptimization_symbolic_undef_bits':n_any,'lowered_domain_property_counts':counts,
        'all_original_states_and_non_decoder_cells_unchanged':True,'native_component_json_matches_proved_component_export_inputs':True,
        'projection_regeneration_matches_source_bound_model':True,'rom_alphabet_matches_certificate':True,
        'must_fix_gaps_remaining_for_this_exact_v3_import':[],
        'transfer_scope':'All state and outputs outside the combinational decoder, including ALU RS state/admission, transfer for unbounded cycles from corresponding native initial states under initial reset and the reset-qualified response domain. No timing/occupancy lemma is assumed.',
        'limitations':['Not a standalone full-core equivalence engine result','Use exact candidate JSON hash; optimized native IL or other variants are not covered','This import does not prove an admission bound or data-fault exclusion','v2 requires a stronger during-reset input premise and does not directly compose with arbitrary initial synchronous memory outputs'],
        'verified_source_and_proof_hashes':{str(p):h for p,h in bindings.items()},
        'additional_review_hashes':{str(p):sha(p) for p in [args.certificate,args.rom_manifest,domain_dir/'export.ys',domain_dir/'lowered.json',domain_dir/'model.smt2',pair_dir/'proof/prepare.ys',pair_dir/'proof/miter.json',candidate_dir/'reference.json',candidate_dir/'candidate.json',Path(__file__)]}}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['status','decoder_changes','native_candidate_sha256','must_fix_gaps_remaining_for_this_exact_v3_import']}))


if __name__=='__main__':main()
