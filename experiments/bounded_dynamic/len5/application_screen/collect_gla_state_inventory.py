#!/usr/bin/env python3
"""Collect source-bound GLA state inventory; invokes no EDA tool or solver."""
import argparse
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path
import re
import tempfile

from gla_state_inventory import inventory,source_owners
from gate_solver import digest,require
from collect_gate_resume import check
from native_gate_bmc import validate_native_gla
from solve_prepared import validate_prepared


def read(path):return json.loads(path.read_text())


def domain_overlap(report,prepared,original,domain):
    """Join projected native Q bits to prepared FF ownership via packed aliases.

    This is an ownership intersection, never a lemma on async2sync raw Q.
    """
    native=next(iter(read(original)['modules'].values()))
    model=read(prepared/'screen.json')['modules']['AdmissionScreen']
    words=domain['projection']['state_words'];wanted={b for w in words for b in w['bits']}
    aliases={b:[] for b in wanted}
    for name,net in native['netnames'].items():
        if 'dut.'+name not in model['netnames']:continue
        other=model['netnames']['dut.'+name]
        require(not net.get('upto',0) and not other.get('upto',0),'Ascending domain alias unsupported')
        require(len(net['bits'])==len(other['bits']),'Native alias width changed')
        for index,bit in enumerate(net['bits']):
            if bit in wanted:aliases[bit].append(('dut.'+name,index+other.get('offset',0)))
    bindings=[];lines=[]
    for wi,word in enumerate(words):
        cell=native['cells'][word['cell']]
        require([cell['connections']['Q'][i] for i in word['original_indices']]==word['bits'],'Domain no longer selects exact native FF Q')
        for bit,position in zip(word['bits'],word['original_indices']):
            require(aliases[bit],'Native field lacks preserved packed alias')
            name,offset=min(aliases[bit],key=lambda x:(len(x[0]),x))
            label=len(bindings);lines.append(f'latch {label} {offset} {name}\n')
            bindings.append({'word':wi,'native_bit':bit,'native_cell':word['cell'],'native_position':position,
                'prepared_alias':name,'prepared_alias_offset':offset})
    with tempfile.TemporaryDirectory() as td:
        fake=Path(td)/'native_alias_map.txt';fake.write_text(''.join(lines));owners,unresolved=source_owners(model,fake)
    covered={}
    for index,binding in enumerate(bindings):
        expected=('$flatten\\dut.'+binding['native_cell'],binding['native_position'])
        require(set(owners[index])=={expected} and not unresolved.get(index),'Native packed alias does not reach the expected FF bit')
        binding['prepared_owner']=owners[index][expected];covered[expected]=binding
    maps={}
    for label in report['maps']:
        rows=[r for r in report['retained_state_rows'] if r['map']==label]
        hits=[{'latch':r['folded_latch'],'group':r['group'],'binding':covered[(o['driver'],o['bit'])]}
            for r in rows for o in r['owners'] if (o['driver'],o['bit']) in covered]
        regstat=[]
        for row in rows:
            if row['group']!='register_scoreboard':continue
            require(len(row['owners'])==1,'Ambiguous regstat ownership')
            name=row['owners'][0]['driver'];match=re.search(r'(?:gen_busy_counters|busy_rob_idx)\[(\d+)\]',name)
            require(match is not None,'Unclassified regstat field');regstat.append((int(match[1]),row))
        permitted=set(domain['output_field_values'])
        maps[label]={'domain_owned_retained_bits':len(hits),'by_group':dict(Counter(h['group'] for h in hits)),
            'retained_domain_bits':hits,'regstat_bits_by_architectural_register':dict(Counter(i for i,r in regstat)),
            'unused_regstat_retained_bits':sum(i not in permitted for i,r in regstat)}
    return {'domain':domain['domain'],'architectural_destination_values':domain['output_field_values'],
        'native_state_words':len(words),'native_state_bits':len(bindings),'bindings':bindings,'maps':maps,
        'scope':'Source ownership intersection only. Visible native domain facts do not imply unconditional domain facts for reset-masked internal async2sync raw Q. No theorem is imported or replayed here.'}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--build-root',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True);a=p.parse_args();b=a.build_root.resolve()
    old=b/'harvard_rom_word_lemmas_alu_mul_prepare_v1';resume=b/'harvard_rom_word_lemmas_alu_mul_gla_resume_v1'
    old_gla=b/'harvard_rom_word_lemmas_alu_mul_gla_v1';native_gla=b/'harvard_rom_inactive_fu_native_gla_v1'
    old_info=check(resume);validate_prepared(old)
    for path,sha in old_info['source_dependencies_sha256'].items():require(digest(Path(path))==sha,'Changed old transitive dependency')
    native_info,native_model,native_deps=validate_native_gla(native_gla);native=Path(native_info['prepared_directory'])
    isa=Path(__file__).resolve().parent.parent/'isa_baseline'
    cert_path=isa/'results/program_registers_certificate_v2.json';cert=read(cert_path)
    original=Path(cert['native_original_json']);require(digest(original)==cert['native_original_sha256'],'Native domain source changed')
    domain_path=b/'rd_domain_symbolic_v5/summary.json';domain=read(domain_path)
    require(domain['status']=='proved' and domain['original_whole_core_sha256']==digest(original),'Domain source/status mismatch')
    prepared_specs=[('old',old,old_gla,b/'gla_state_inventory_v2',{'initial':old_gla/'final_map.aig','resumed':resume/'final_map.aig'}),
        ('native',native,native_gla,b/'gla_native_state_inventory_v1',{'native':native_gla/'final_map.aig'})]
    audits={};sources={};reports={}
    for label,prepared,gla,export,maps in prepared_specs:
        exp=read(export/'export_summary.json');require(exp['same_aig_bytes'] and exp['execution']['returncode']==0 and not exp['execution']['timeout'],'Failed source-map export')
        require((export/'screen.aig').read_bytes()==(prepared/'screen.aig').read_bytes(),'Symbol-map export changed AIG')
        require(digest(prepared/'screen.aig')==exp['source_aig_sha256'],'Changed source AIG')
        require(digest(export/'symbol_export.log')==exp['execution']['log_sha256'],'Changed symbol export log')
        require(digest(Path(exp['execution']['executable']))==exp['execution']['executable_sha256'],'Changed exporter tool')
        require(read(export/'inventory.json')['script_sha256']==digest(Path(__file__).with_name('gla_state_inventory.py')),'Inventory parser changed')
        result=inventory(prepared,export/'latch_map.txt',gla/'folded.aig',maps)
        recorded=read(export/'inventory.json');recorded.pop('script_sha256')
        require(result==recorded,'Recomputed retained-state inventory differs')
        reports[label]=result;audits[label]=domain_overlap(result,prepared,original,domain)
        for file in [prepared/'screen.json',prepared/'screen.aig',gla/'folded.aig',export/'latch_map.txt',export/'inventory.json',
                     export/'symbol_export.ys',export/'symbol_export.log',export/'export_summary.json',*maps.values()]:sources[str(file)]=digest(file)
    out=a.output.resolve();out.mkdir(parents=True,exist_ok=False);files=[]
    def keep(source,name,raw=None):
        original_bytes=source.read_bytes() if raw is None else raw
        compress=len(original_bytes)>100000
        if compress:name+='.gz'
        dest=out/name;dest.parent.mkdir(parents=True,exist_ok=True)
        dest.write_bytes(gzip.compress(original_bytes,mtime=0) if compress else original_bytes)
        files.append({'path':name,'sha256':digest(dest),'source':str(source),'source_sha256':digest(source),
            'content_sha256':hashlib.sha256(original_bytes).hexdigest(),'gzip':compress,
            'selection':'all lines beginning latch only' if raw is not None else 'complete file'})
    for label,prepared,gla,export,maps in prepared_specs:
        for name in ['inventory.json','export_summary.json','symbol_export.ys','symbol_export.log']:
            keep(export/name,label+'/'+name)
        raw=''.join(line for line in (export/'latch_map.txt').read_text().splitlines(keepends=True) if line.startswith('latch ')).encode()
        keep(export/'latch_map.txt',label+'/latch_only_map.txt',raw)
        keep(prepared/'summary.json',label+'/prepared_summary.json');keep(gla/'summary.json',label+'/gla_summary.json')
    keep(resume/'summary.json','old/resume_summary.json')
    for name in ['fold_symbol_export.json','fold_symbol_export.log']:
        keep(b/'gla_state_inventory_v2'/name,'old/'+name)
    here=Path(__file__).resolve().parent
    helpers=['gla_state_inventory.py','collect_gla_state_inventory.py','gate_resume.py','gate_solver.py',
        'solve_prepared.py','collect_gate_resume.py','native_gate_solver.py','native_gate_bmc.py']
    for name in helpers:keep(here/name,'helpers/'+name);sources[str(here/name)]=digest(here/name)
    keep(here.parents[3]/'tests/unit/test_gla_state_inventory.py','test_gla_state_inventory.py')
    keep(cert_path,'domain/program_registers_certificate_v2.json');keep(domain_path,'domain/rd_domain_summary.json')
    for label,data in audits.items():(out/(label+'_domain_overlap.json')).write_text(json.dumps(data,indent=2)+'\n')
    # Authoritative provenance checks again after all source parsing/copying.
    check(resume);validate_prepared(old);validate_native_gla(native_gla)
    for path,sha in {**old_info['source_dependencies_sha256'],**native_deps,**sources}.items():
        require(digest(Path(path))==sha,'Dependency changed during inventory')
    manifest={'status':'source_bound_inventory_only','solver_invoked':False,'new_query_or_hardware_change':False,
        'all_retained_state_resolved':all(not m['unresolved_retained_latches'] for r in reports.values() for m in r['maps'].values()),
        'post_collection_dependency_checks_passed':True,'source_sha256':sources,
        'old_dependencies_sha256':old_info['source_dependencies_sha256'],'native_dependencies_sha256':native_deps,
        'domain_certificate_sha256':digest(cert_path),'domain_summary_sha256':digest(domain_path),
        'limitations':'No solver or theorem replay. Domain overlap is an exact native-field ownership count, not an import certificate. Source/folded latch ordering is structurally checked. Raw reset-masked state is not equated to visible outputs. Cone counts overlap; map models/stopping depths differ; counts are not area or proof-strength comparisons.',
        'artifacts':files}
    (out/'PROVENANCE.json').write_text(json.dumps(manifest,indent=2)+'\n')
    (out/'SHA256SUMS').write_text(''.join(f'{digest(f)}  {f.relative_to(out)}\n' for f in sorted(out.rglob('*')) if f.is_file()))
    print(json.dumps({'files':sum(f.is_file() for f in out.rglob('*')),'bytes':sum(f.stat().st_size for f in out.rglob('*') if f.is_file()),
        'overlap':{label:{k:v['domain_owned_retained_bits'] for k,v in data['maps'].items()} for label,data in audits.items()}}))


if __name__=='__main__':main()
