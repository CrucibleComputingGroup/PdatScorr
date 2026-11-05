#!/usr/bin/env python3
"""Package existing GLA toys, source audit, and one immutable query diagnostic."""
import argparse
import gzip
import json
from pathlib import Path
import re
import sys

HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE.parents[3]),str(HERE)]
from odc.temporal import digest
from gate_solver import header, verdict
from solve_prepared import validate_prepared


def load(path): return json.loads(path.read_text())


def check_result(directory):
    record=load(directory/'summary.json')
    for name,expected in record['artifacts_sha256'].items():
        assert digest(directory/name)==expected,name
    assert digest(Path(record['input_aig']))==record['input_aig_sha256']
    assert digest(directory/'gate_solver.py')==record['script_sha256']
    raw=verdict(record['execution'],(directory/'gla.log').read_text(),record['raw_status'])
    if record['status']=='counterexample_in_query_model':
        assert raw=='counterexample_pending_validation'
        assert 'And  AIG: The cex is correct.' in (directory/'validate_cex.log').read_text()
        assert (directory/'counterexample.aiw').exists()
    else:assert raw==record['status']
    return record


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--toys',type=Path,required=True);ap.add_argument('--query',type=Path,required=True)
    ap.add_argument('--source-audit',type=Path,required=True);ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();toys=args.toys.resolve();query=args.query.resolve();audit=args.source_audit.resolve()
    toy_summary=load(toys/'summary.json');assert toy_summary['status']=='all_four_toys_passed'
    for case in toy_summary['cases']:
        result=check_result(toys/case['case']/'gla')
        assert result['status']==case['expected'] and digest(toys/case['case']/'gla/summary.json')==case['result_summary_sha256']
    result=check_result(query);prepared=Path(result['prepared_directory']);model=validate_prepared(prepared)
    assert digest(prepared/'summary.json')==result['prepared_summary_sha256']
    assert result['input_aig_sha256']==model['aig_sha256']
    source=load(audit/'summary.json');assert source['installed_abc_sha256']==result['execution']['executable_sha256']
    assert toy_summary['gate_solver_sha256']==result['script_sha256']
    out=args.output.resolve();out.mkdir(parents=True,exist_ok=False);records=[]
    def keep(path,relative):
        raw=path.read_bytes();compress=path.suffix=='.aig' or len(raw)>100_000
        if compress:relative+='.gz'
        dest=out/relative;dest.parent.mkdir(parents=True,exist_ok=True)
        dest.write_bytes(gzip.compress(raw,mtime=0) if compress else raw)
        records.append({'path':relative,'source':str(path),'sha256':digest(dest),'source_sha256':digest(path),'gzip':compress})
    for directory,prefix in ((toys,'toys'),(query,'query'),(audit,'source_audit')):
        for path in sorted(directory.rglob('*')):
            if path.is_file():keep(path,prefix+'/'+str(path.relative_to(directory)))
    keep(prepared/'summary.json','prepared_summary.json')
    keep(Path(__file__),'collector_source.py')
    log=(query/'gla.log').read_text()
    timeout=re.search(r'GLA reached timeout (\d+) sec in frame (\d+) with a (\d+)-stable abstraction',log)
    calls=re.search(r'Concurrent calls = (\d+)',log)
    record={'status':result['status'],'accepted_optimization':False,
        'tiny_validation':'Two unbounded positive proofs and two verified concrete counterexamples, including8constraints and arbitrary initial FF state',
        'prepared_source_json_sha256':model['source_json_sha256'],'native_hardware_json_sha256':model['core_json_sha256'],
        'input_aig_sha256':result['input_aig_sha256'],'folded_header':result.get('folded_header'),
        'final_abstracted_header':result.get('abstracted_header'),'proof_thread_calls':int(calls[1]) if calls else None,
        'timeout_frame':int(timeout[2]) if timeout else None,'stable_frames_at_timeout':int(timeout[3]) if timeout else None,
        'interpretation':'The abstraction is a proof-only overapproximation, not optimized hardware. Stability or a smaller map is not a certificate. An unbounded verdict requires the explicit GLA proof terminal and snl_UNSAT. This diagnostic added no environmental or internal premises.',
        'source_identity_caveat':source['source_identity_caveat'],'artifacts':records}
    (out/'PROVENANCE.json').write_text(json.dumps(record,indent=2)+'\n')
    (out/'SHA256SUMS').write_text(''.join(f'{digest(p)}  {p.relative_to(out)}\n' for p in sorted(out.rglob('*')) if p.is_file()))
    print(json.dumps({'status':result['status'],'files':len(records),'bytes':sum(p.stat().st_size for p in out.rglob('*') if p.is_file())}))


if __name__=='__main__':main()
