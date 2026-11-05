#!/usr/bin/env python3
"""Test whether the installed GLA-refinement CLI preserves a concrete CEX.

Only two previously qualified tiny controls are probed. No target refinement
or follow-up safety search is launched by this compatibility diagnostic.
"""
import argparse
import json
from pathlib import Path
import re

from gate_pdr import rederive_map
from gate_solver import digest,quote,require,run_command


def read(path):return json.loads(path.read_text())


def probe(toy,out,*,spurious,abc):
    out.mkdir();pdr=read(toy/'pdr/summary.json')
    require(pdr['status']=='counterexample_in_abstraction_only','Missing validated tiny abstraction CEX')
    aig=Path(pdr['input_aig']);status=toy/'pdr/pdr.status'
    require(digest(aig)==pdr['input_sha256'],'Changed tiny abstraction')
    for name,sha in pdr['artifacts_sha256'].items():require(digest(toy/'pdr'/name)==sha,'Changed tiny CEX artifact')
    map_path=toy/'bounded_map.aig' if spurious else toy/'gla/abstraction_map.aig'
    original=read(toy/('unbounded' if spurious else 'gla')/'summary.json')
    require(original['status']==('proved_safety_query_only' if spurious else 'counterexample_in_query_model'),'Wrong independently classified tiny control')
    replay=rederive_map(map_path,aig,out/'map_replay',abc=abc)
    inputs={str(p):digest(p) for p in [map_path,aig,status,toy/'pdr/summary.json']}
    validate=run_command([abc,'-c',f'read_aiger {quote(aig)}; &get; read_status {quote(status)}; testcex'],out/'input_cex_validation.log',10)
    text=(out/'input_cex_validation.log').read_text()
    require(validate['returncode']==0 and not validate['timeout'] and re.search(r'And\s+AIG: The cex is correct\.',text),'Input CEX/model mismatch')
    command=f'&read {quote(map_path)}; read_status {quote(status)}; &gla_refine -F 0 -G 0 -v; write_status {quote(out/"refined.status")}; &write -s {quote(out/"refined_map.aig")}'
    execution=run_command([abc,'-c',command],out/'refine.log',15)
    log=(out/'refine.log').read_text();returned=(out/'refined.status').read_text() if (out/'refined.status').exists() else ''
    require(execution['returncode']==0 and not execution['timeout'],'Tiny refinement command failed')
    require('Gia_ManNewRefine(): The initial counter-example is correct.' in log and
            'Shortened CEX holds for the abstraction of the fast-forwarded model.' in log and
            not re.search(r'invalid|do not match|missing|no counter-example|error',log,re.I),'Refinement did not bind the exact tiny CEX/map')
    require(all(digest(Path(p))==sha for p,sha in inputs.items()),'Tiny source artifact changed')
    result={'known_original_result':'safe' if spurious else 'concrete_counterexample',
        'input_abstraction_cex_validated':True,'gate_map_replay':replay,'input_sha256':inputs,
        'execution':execution,'raw_returned_status':returned,
        'output_status_is_unknown':returned.split()[0]=='snl_UNK' if returned else False,
        'concrete_witness_returned':'snl_SAT' in returned and len(returned.splitlines())>1 and returned.splitlines()[1]!='NULL',
        'output_map_sha256':digest(out/'refined_map.aig') if (out/'refined_map.aig').exists() else None,
        'map_changed':digest(out/'refined_map.aig')!=digest(map_path) if (out/'refined_map.aig').exists() else None}
    (out/'summary.json').write_text(json.dumps(result,indent=2)+'\n');return result


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--toys',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True);p.add_argument('--abc',default='/usr/local/bin/abc')
    a=p.parse_args();out=a.output.resolve();out.mkdir(parents=True,exist_ok=False)
    results={name:probe(a.toys.resolve()/name,out/name,spurious=name=='spurious',abc=a.abc) for name in ('spurious','negative')}
    record={'status':'refinement_cli_cannot_supply_validated_concrete_verdict' if all(r['output_status_is_unknown'] and not r['concrete_witness_returned'] for r in results.values()) else 'requires_further_review',
        'cases':results,'target_refinement_launched':False,'accepted_optimization':False,
        'source_sha256':digest(Path(__file__)),
        'interpretation':'The installed command binds the supplied abstract CEX/map, but loses the concrete result/witness for both known-safe and known-unsafe originals. Returned maps can be diagnostic only. No target query is authorized by this probe.'}
    (out/'refine_map_probe.py').write_bytes(Path(__file__).read_bytes());(out/'summary.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({'status':record['status'],'target_refinement_launched':False}))


if __name__=='__main__':main()
