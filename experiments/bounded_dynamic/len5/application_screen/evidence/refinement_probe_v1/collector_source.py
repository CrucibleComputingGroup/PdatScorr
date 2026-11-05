#!/usr/bin/env python3
"""Preserve the failed-closed tiny refinement plumbing probe; run no tools."""
import argparse
import gzip
import json
from pathlib import Path
import re

from gate_solver import digest,require
from solve_prepared import validate_prepared


def read(path):return json.loads(path.read_text())


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--probe',required=True,type=Path)
    p.add_argument('--toys',required=True,type=Path);p.add_argument('--target-bmc',required=True,type=Path)
    p.add_argument('--abc-source',required=True,type=Path);p.add_argument('--output',required=True,type=Path)
    a=p.parse_args();probe=a.probe.resolve();toys=a.toys.resolve();target=read(a.target_bmc/'summary.json')
    validate_prepared(Path(target['source_prepared_directory']))
    for path,sha in target['source_dependencies_sha256'].items():require(digest(Path(path))==sha,'Target dependency changed')
    out=a.output.resolve();out.mkdir(parents=True,exist_ok=False);files=[]
    def keep(path,name):
        data=path.read_bytes();compressed=path.suffix=='.aig'
        if compressed:name+='.gz'
        dest=out/name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(gzip.compress(data,mtime=0) if compressed else data)
        files.append({'path':name,'sha256':digest(dest),'source':str(path),'source_sha256':digest(path),'gzip':compressed})
    cases={}
    for name in ('spurious','negative'):
        directory=probe/name;log=(directory/'refine.log').read_text();status=(directory/'refined.status').read_text()
        require('Gia_ManNewRefine(): The initial counter-example is correct.' in log,'CEX never checked')
        require(status=='snl_UNK 0 unknown\nNULL\nNULL\n','Unexpected returned status')
        validation=(directory/'input_cex_validation.log').read_text()
        require(re.search(r'And\s+AIG: The cex is correct\.',validation),'Prior exact abstraction validation missing')
        mapping_warning='Structural hashing enabled while reading AIGER invalidated the mapping.' in log
        known=read(toys/name/('unbounded' if name=='spurious' else 'gla')/'summary.json')
        cases[name]={'original_independent_status':known['status'],'returned_status':status,
            'exact_input_abstraction_cex_validation_present':True,'native_mapping_warning':mapping_warning,
            'internal_log_reports_real_counterexample':'True counter-example detected in frame 1.' in log,
            'concrete_witness_exported':False,'qualification':'rejected_mapping_warning' if mapping_warning else 'map_bound_but_no_concrete_verdict'}
        for path in sorted(directory.rglob('*')):
            if path.is_file():keep(path,'probe/'+name+'/'+str(path.relative_to(directory)))
        old=toys/name
        for path,label in [(old/'pdr/summary.json','prior_abstract_cex_summary.json'),(old/'pdr/pdr.status','input_cex.status'),
            (old/('bounded_map.aig' if name=='spurious' else 'gla/abstraction_map.aig'),'input_map.aig'),
            (old/('unbounded' if name=='spurious' else 'gla')/'summary.json','prior_original_summary.json')]:
            keep(path,'prior_controls/'+name+'/'+label)
    require(cases['negative']['native_mapping_warning'],'Expected failed-closed binding warning missing')
    source=a.abc_source.resolve();abs_source=source/'src/proof/abs/absOut.c';command_source=source/'src/base/abci/abc.c'
    keep(abs_source,'abc_source/absOut.c');keep(source/'copyright.txt','abc_source/copyright.txt')
    text=command_source.read_text();start=text.index('int Abc_CommandAbc9GlaRefine( Abc_Frame_t * pAbc, int argc, char ** argv )\n{')
    end=text.index('\n/**Function',start)
    (out/'abc_source/command_excerpt.c').write_text(text[start:end]+'\n')
    here=Path(__file__).resolve().parent
    keep(here/'refine_map_probe.py','refine_map_probe.py');keep(Path(__file__).resolve(),'collector_source.py')
    keep(a.target_bmc.resolve()/'summary.json','validated_target_bmc_summary.json')
    report={'status':'target_refinement_not_launched_due_to_failed_plumbing_controls','target_refinement_launched':False,
        'accepted_optimization':False,'target_cex_still_abstraction_only':True,'target_dependencies_revalidated':True,
        'cases':cases,'observed_probe_process_exit':1,
        'observed_probe_exception':'ValueError: Refinement did not bind the exact tiny CEX/map',
        'source_analysis':{'command':'Abc_CommandAbc9GlaRefine calls Gia_ManNewRefine, then replaces the global CEX with pGia->pCexSeq.',
            'function':'Gia_ManNewRefine validates the abstract CEX then invokes bounded GLA, destroys pNew without moving its CEX to p, and unconditionally returns -1.',
            'source_checkout_commit':'5d51a5e420f5de493d07bf61109a977248c86ffb','absOut_sha256':digest(abs_source),
            'abc_c_sha256':digest(command_source),'binary_sha256':digest(Path('/usr/local/bin/abc')),
            'binding_caveat':'Local source inspection is consistent with observed installed-binary behavior; no claim that this checkout alone proves binary build provenance.'},
        'conclusion':'The tiny known-real case emits a true-CEX log but loses SAT status and witness, so testcex cannot validate a concrete original-model result. A mapping-invalidated warning separately fails the strict binding guard. No target attempt, weaker guard, further search, or native claim follows.',
        'artifacts':files}
    (out/'PROVENANCE.json').write_text(json.dumps(report,indent=2)+'\n')
    (out/'SHA256SUMS').write_text(''.join(f'{digest(f)}  {f.relative_to(out)}\n' for f in sorted(out.rglob('*')) if f.is_file()))
    print(json.dumps({'status':report['status'],'files':sum(f.is_file() for f in out.rglob('*')),
        'bytes':sum(f.stat().st_size for f in out.rglob('*') if f.is_file())}))


if __name__=='__main__':main()
