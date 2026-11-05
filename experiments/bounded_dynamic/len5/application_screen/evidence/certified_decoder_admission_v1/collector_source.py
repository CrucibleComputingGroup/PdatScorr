#!/usr/bin/env python3
"""Collect an existing certified-decoder admission query; run no experiments."""
import argparse
import copy
import gzip
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path):
    return json.loads(path.read_text())


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();src=args.build.resolve();out=args.output.resolve()
    summary=load(src/'summary.json');bound=summary['certified_decoder_import']
    assert summary['accepted_optimization'] is False and summary['abstraction_mode']=='none'
    assert summary['instruction_model']=='immutable_rom' and summary['instruction_fault_payload']=='zero'
    assert summary['status']=='unknown'
    for key,name in [('source_json','source.json'),('core_json','core.json'),('core','core.v'),
        ('harness','AdmissionScreen.sv'),('script','formal_screen.py'),('temporal_helper','temporal.py'),
        ('rom_helper','program_rom.py'),('rom_image','program.hex'),('aig','screen.aig')]:
        assert sha(src/name)==summary[key+'_sha256']
    cdir=src/'certified_decoder';cert=load(cdir/'certificate.json')
    assert cert==load(cdir/'revalidated_certificate.json')
    assert sha(cdir/'certificate.json')==bound['certificate_sha256']
    assert sha(cdir/'revalidated_certificate.json')==bound['fresh_certificate_sha256']
    assert sha(cdir/'certifier_source.py')==bound['certifier_sha256']==cert['certifier_sha256']
    assert sha(cdir/'importer_source.py')==bound['importer_sha256']
    assert sha(src/'source.json')==cert['native_original_sha256']==bound['original_native_sha256']
    assert sha(cdir/'native_candidate.json')==cert['native_candidate_sha256']==bound['candidate_native_sha256']
    observed=load(src/'core.json');candidate=load(cdir/'native_candidate.json')
    m=observed['modules']['datapath']
    probes={}
    for alias,signal in [('probe_insert','insert'),('probe_index','new_idx')]:
        bits=m['netnames']['u_backend.u_exec_stage.u_alu_unit.u_arith_rs.'+signal]['bits']
        probes[alias]=m['ports'].pop(alias)
        assert probes[alias]=={'direction':'output','bits':bits}
    assert observed==candidate,'Only the two native observation ports may be added after import'
    screen=load(src/'screen.json')['modules']['AdmissionScreen']
    counts={kind:sum(c['type']=='$'+kind for c in screen['cells'].values()) for kind in ('assert','assume')}
    assert counts=={'assert':3,'assume':1}
    for key in ('source_export','prepare','export','pdr'):
        record=summary[key]
        assert record['returncode']==0 and not record['timeout']
        assert sha(Path(record['log']))==record['log_sha256']
    assert sha(Path(bound['verifier_execution']['log']))==bound['verifier_execution']['log_sha256']
    log=(src/'pdr.log').read_text()
    assert 'Property UNDECIDED.' in log and 'was asserted' not in log and 'Property proved.' not in log
    out.mkdir(parents=True)
    records=[]
    def keep(path,rel):
        raw=path.read_bytes();compress=path.suffix=='.log' and len(raw)>100000
        if compress:rel+='.gz'
        dest=out/rel;dest.parent.mkdir(parents=True,exist_ok=True)
        dest.write_bytes(gzip.compress(raw,mtime=0) if compress else raw)
        records.append({'path':rel,'sha256':sha(dest),'source':str(path),
            'source_sha256':sha(path),'gzip':compress})
    for path in sorted(src.iterdir()):
        if path.is_file() and (path.suffix in ('.py','.ys','.log','.sv','.hex') or path.name in ('summary.json','rom.json')):
            keep(path,'run/'+path.name)
    for path in sorted(cdir.iterdir()):
        if path.is_file() and path.name!='native_candidate.json':keep(path,'run/certified_decoder/'+path.name)
    keep(Path(__file__),'collector_source.py')
    large={name:{'path':str(src/name),'sha256':sha(src/name),'bytes':(src/name).stat().st_size}
        for name in ('source.json','core.json','core.v','screen.json','screen.aig','certified_decoder/native_candidate.json')}
    audit={'status':'unknown_no_accepted_optimization','accepted_optimization':False,
        'certificate_replay_identical':True,'original_native_source_hash_matches':True,
        'certified_candidate_plus_exact_native_probes_only':True,'native_probe_ports':probes,
        'assumptions_added_by_import':0,'query_property_counts':counts,
        'data_abstraction':'none','instruction_platform':'Immutable Harvard ROM; aligned mapped words or zero fault payload; common native initial reset',
        'pdr_seconds':summary['pdr']['seconds'],'aig_header':summary['aig_header'],
        'runtime_importer_sha256':bound['importer_sha256'],
        'current_importer_sha256':sha(HERE/'certified_decoder.py'),
        'post_run_hardening':'Current importer also captures source bytes and rejects changes during verifier replay. Archived runtime inputs/candidate/certificate all match the exact certified hashes; no target rerun was needed.',
        'interpretation':'The certified program-only substitution is used as proof preprocessing. The timing/admission property remains unproved; no timing-induced hardware removal or area reduction follows.',
        'large_artifacts':large,'artifacts':records}
    (out/'PROVENANCE.json').write_text(json.dumps(audit,indent=2)+'\n')
    (out/'SHA256SUMS').write_text(''.join(f'{sha(p)}  {p.relative_to(out)}\n' for p in sorted(out.rglob('*')) if p.is_file()))
    print(json.dumps({'status':audit['status'],'files':len(records),'bytes':sum(p.stat().st_size for p in out.rglob('*') if p.is_file())}))


if __name__=='__main__':
    main()
