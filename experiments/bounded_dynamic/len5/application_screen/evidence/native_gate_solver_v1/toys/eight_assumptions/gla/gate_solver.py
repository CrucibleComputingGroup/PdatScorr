#!/usr/bin/env python3
"""ABC gate-level abstraction diagnostic on an immutable safety-query AIG.

Fold constraints into the property before converting to GIA. Abstraction
stability and bounded success are never proofs. No hardware is generated.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE.parents[3]), str(HERE)]
from odc.temporal import (checked_yosys, digest, formal_lower_command, formal_prepare_command,
    run_command, validate_single_clock, yosys_path)
from solve_prepared import validate_prepared


def require(condition, message):
    if not condition: raise ValueError(message)


def quote(path):
    value = str(Path(path).resolve())
    require(not any(c in value for c in ('"', '\n', '\r', ';')), 'Unsupported ABC command path')
    return '"'+value+'"'


def header(path):
    with Path(path).open('rb') as stream: values=stream.readline().decode('ascii').split()
    require(values[0] == 'aig' and 6 <= len(values) <= 10, 'Expected binary AIGER')
    return values


def verdict(execution, log, status):
    """Require the engine's unbounded terminal result and independent status."""
    if execution['timeout'] or execution['returncode'] != 0: return 'unknown'
    if re.search(r'\b(error|failed|assertion failure|segmentation fault)\b', log, re.I): return 'error'
    token = status.split()[0] if status.strip() else None
    proved = re.search(r'GLA completed \d+ frames and proved abstraction derived in frame \d+', log)
    trivial = 'Sequential miter is trivially UNSAT.' in log
    cex = re.search(r'True counter-example detected in frame \d+', log) or 'Sequential miter is trivially SAT.' in log
    if token == 'snl_UNSAT' and (proved or trivial) and not cex:
        return 'proved_safety_query_only'
    if token == 'snl_SAT' and cex and not proved and not trivial:
        return 'counterexample_pending_validation'
    return 'unknown'


def prepare_toy(source, directory, *, yosys, timeout=15):
    """Same safe frontend/zinit semantics as the native query, for regressions."""
    directory=Path(directory).resolve();directory.mkdir(parents=True,exist_ok=False)
    sv=directory/'toy.sv';sv.write_text(source)
    script=f'read_verilog -formal -sv {yosys_path(sv)}\n'+formal_prepare_command('GateToy')+formal_lower_command(yosys)
    script+='memory_map\nsetundef -anyseq\nopt_clean\nasync2sync\ndffunmap\nsetundef -anyseq\n'
    script+=f'write_json {yosys_path(directory/"model.json")}\n'
    prepared=checked_yosys(yosys,script,directory,'prepare',timeout)
    model=json.loads((directory/'model.json').read_text());clocks=validate_single_clock(model,'GateToy')
    script=f'read_json {yosys_path(directory/"model.json")}\nformalff -clk2ff\nsetundef -anyseq\nopt -keepdc\ntechmap\nopt -keepdc\nsetundef -anyseq\naigmap\n'
    script+=f'write_aiger -zinit -symbols {yosys_path(directory/"query.aig")}\n'
    exported=checked_yosys(yosys,script,directory,'export',timeout)
    record={'source_sha256':digest(sv),'prepare':prepared,'export':exported,'clock_model':clocks,
        'aig_sha256':digest(directory/'query.aig'),'aig_header':header(directory/'query.aig'),
        'initial_state':'Native unknown FF initial values remain arbitrary through zinit input encoding'}
    (directory/'preparation.json').write_text(json.dumps(record,indent=2)+'\n')
    return directory/'query.aig',record


def run_gla(aig, directory, *, abc='/usr/local/bin/abc', timeout=120):
    aig=Path(aig).resolve();directory=Path(directory).resolve();directory.mkdir(parents=True,exist_ok=False)
    source_hash=digest(aig);script_hash=digest(Path(__file__))
    (directory/'gate_solver.py').write_bytes(Path(__file__).read_bytes())
    folded=directory/'folded.aig';mapped=directory/'abstraction_map.aig';final=directory/'final_map.aig'
    # &gla sees exactly one ordinary bad output and no unconsumed AIGER
    # constraints. fold/orpos is identical to the direct PDR/BMC controls.
    command=(f'read_aiger {quote(aig)}; fold; orpos; &get; &write -s {quote(folded)}; '
             f'&gla -q -T {timeout} -v -m -A {quote(mapped)} -L {quote(directory/"gla.status")}; '
             f'write_status {quote(directory/"final.status")}; &write -s {quote(final)}')
    execution=run_command([abc,'-c',command],directory/'gla.log',timeout+5)
    log=(directory/'gla.log').read_text()
    status=(directory/'final.status').read_text() if (directory/'final.status').exists() else ''
    result=verdict(execution,log,status)
    record={'status':result,'accepted_optimization':False,'engine':'ABC &gla -q',
        'input_aig':str(aig),'input_aig_sha256':source_hash,'input_header':header(aig),
        'script_sha256':script_hash,'execution':execution,'raw_status':status,
        'fold_semantics':'AIGER constraints folded first, all bad outputs ORed, then &get; no extra internal premises',
        'interpretation':'Only explicit threaded-PDR unbounded proof or trivial constant-zero miter can prove safety. A stable abstraction, bounded checks, and timeout are inconclusive. Maps are proof-only artifacts, never hardware.'}
    if folded.exists():
        values=header(folded)
        require(int(values[4])==1 and (len(values)<8 or int(values[7])==0), 'GLA input must have one output and no remaining constraints')
        record['folded_header']=values
    if result=='counterexample_pending_validation':
        # The status stores the original folded model's concrete trace, not an
        # arbitrary trace of a relaxed abstraction. Verify before writing it.
        check=(f'read_aiger {quote(folded)}; &get; read_status {quote(directory/"final.status")}; testcex; '
               f'write_cex -a {quote(directory/"counterexample.aiw")}')
        validation=run_command([abc,'-c',check],directory/'validate_cex.log',15)
        text=(directory/'validate_cex.log').read_text()
        record['counterexample_validation']=validation
        record['status']='counterexample_in_query_model' if (validation['returncode']==0 and not validation['timeout'] and
            re.search(r'And\s+AIG: The cex is correct\.',text) and
            not re.search(r'\b(error|failed)\b',text,re.I) and (directory/'counterexample.aiw').exists()) else 'error'
    # Derivation is a model export only. If GLA was interrupted, the last map
    # dumped at a stable point is retained; it does not constitute a proof.
    map_source=final if final.exists() else mapped
    if map_source.exists() and record['status']!='counterexample_in_query_model':
        derive=f'&read {quote(map_source)}; &gla_derive; &ps; &write -s {quote(directory/"abstracted.aig")}'
        record['derive']=run_command([abc,'-c',derive],directory/'derive.log',20)
        if (directory/'abstracted.aig').exists():record['abstracted_header']=header(directory/'abstracted.aig')
        record['dumped_model_scope']='Recorded map is the last available map; it need not be the exact earlier map solved by the background thread. The verdict refers to the source-bound original folded query.'
    record['artifacts_sha256']={p.name:digest(p) for p in directory.iterdir() if p.is_file()}
    if digest(aig)!=source_hash or digest(Path(__file__))!=script_hash:
        record.update(status='error',error='Input AIG or driver changed during run')
    (directory/'summary.json').write_text(json.dumps(record,indent=2)+'\n')
    return record


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--prepared',type=Path,required=True);ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--timeout',type=int,default=120);ap.add_argument('--abc',default='/usr/local/bin/abc')
    args=ap.parse_args();require(args.timeout>0,'Positive budget required')
    prepared=args.prepared.resolve();summary=validate_prepared(prepared);binding=digest(prepared/'summary.json')
    require(summary['abstraction_mode']=='alu_mul' and summary['query_property_counts']=={'assert':3,'assume':8,'cover':0},
            'This diagnostic is restricted to the reviewed ALU/multiplier theorem composition')
    record=run_gla(prepared/'screen.aig',args.output,abc=args.abc,timeout=args.timeout)
    record['prepared_summary_sha256']=binding;record['prepared_directory']=str(prepared)
    try:
        validate_prepared(prepared)
        require(digest(prepared/'summary.json')==binding,'Preparation changed during GLA')
    except (ValueError,OSError) as error:record.update(status='error',error=str(error))
    (args.output/'summary.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({'status':record['status'],'accepted_optimization':False}))


if __name__=='__main__':main()
