#!/usr/bin/env python3
"""Validate and run word-level Pono MBIC3 on an immutable prepared query.

No hardware transformation or premise is added. Three assertions are combined
into one BTOR bad condition; all eight original constraints remain constraints.
Only explicit unbounded UNSAT plus successful invariant checking is a proof.
"""
from __future__ import annotations
import argparse
from collections import Counter
import json
from pathlib import Path
import re
import shutil
import sys

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE.parents[3]), str(HERE)]
import odc.temporal as temporal
from odc.temporal import (checked_yosys, digest, formal_prepare_command,
    formal_lower_command, run_command, validate_single_clock, yosys_path)

OSS = Path('/home/allenjin/Projects/DAC_pscorr/tools/oss-cad-suite-20261104/oss-cad-suite/bin')
ENGINE = ['-e', 'mbic3', '--smt-solver', 'btor', '--pseudo-init-prop',
          '--check-invar', '-v', '1']


def require(ok, reason):
    if not ok: raise ValueError(reason)


def read(path): return json.loads(Path(path).read_text())


def property_counts(design, top):
    cells = design['modules'][top]['cells']
    return {kind:sum(cell['type'] == '$'+kind for cell in cells.values())
            for kind in ('assert', 'assume', 'cover')}


def check_model(design, top, expected):
    require(set(design['modules']) == {top}, 'Model is not flat')
    require(property_counts(design, top) == expected, 'Changed assertions/assumptions')
    require(not any(bit in ('x','z') for cell in design['modules'][top]['cells'].values()
        for bits in cell['connections'].values() for bit in bits), 'Literal X/Z in prepared model')
    return validate_single_clock(design, top)


def btor_inventory(path):
    rows = [line.split(';',1)[0].split() for line in path.read_text().splitlines()]
    rows = [row for row in rows if row]
    require(all(row[0].isdigit() for row in rows), 'Invalid BTOR records')
    counts = Counter(row[1] for row in rows)
    widths = {int(row[0]):int(row[3]) for row in rows if row[1:3] == ['sort','bitvec']}
    return {'operators':dict(counts), 'bad':counts['bad'], 'constraint':counts['constraint'],
        'state_bits':sum(widths[int(row[2])] for row in rows if row[1] == 'state'),
        'input_bits':sum(widths[int(row[2])] for row in rows if row[1] == 'input'),
        'states':[row for row in rows if row[1]=='state'],
        'initializers':[row for row in rows if row[1]=='init']}


def export_btor(source, top, directory, yosys, expected, timeout):
    design = read(source); clock = check_model(design,top,expected)
    script = f'read_json {yosys_path(source)}\ncheck -assert\n'
    # The input has already undergone the safe undefined-value frontend. A new
    # setundef cannot turn an arbitrary initial state into a chosen value.
    script += 'formalff -clk2ff\nsetundef -anyseq\n'
    script += f'write_json {yosys_path(directory/"exported.json")}\n'
    # write_btor's option parser treats quotes in -i/-ywmap as literal bytes.
    # Restrict these two paths instead of relying on shell or Yosys escaping.
    require(re.fullmatch(r'[A-Za-z0-9_./-]+',str(directory)) is not None, 'Unsafe BTOR auxiliary path')
    script += f'write_btor -s -v -i {directory/"model.info"} -ywmap {directory/"model.ywb"} {yosys_path(directory/"model.btor2")}\n'
    execution = checked_yosys(yosys,script,directory,'export',timeout)
    exported = read(directory/'exported.json')
    require(property_counts(exported,top)==expected, 'Export changed semantic property counts')
    require(not any(bit in ('x','z') for cell in exported['modules'][top]['cells'].values()
        for bits in cell['connections'].values() for bit in bits), 'Export introduced literal X/Z')
    inv = btor_inventory(directory/'model.btor2')
    require(inv['bad']==1 and inv['constraint']==expected['assume'], 'BTOR dropped or added properties/constraints')
    return {'source_sha256':digest(source),'clock_model':clock,'property_counts':expected,
        'export':execution,'exported_json_sha256':digest(directory/'exported.json'),
        'btor_sha256':digest(directory/'model.btor2'),'btor':inv}


def classify(execution, text):
    statuses = re.findall(r'(?m)^(sat|unsat|unknown|error)$',text)
    if execution['timeout']: return 'unknown_timeout'
    if (execution['returncode']==1 and statuses==['unsat'] and
        'Invariant Check PASSED' in text and
        all(token in text for token in ('INVARCHECK: init |= inv...OK',
            "INVARCHECK: inv & trans |= inv'...OK", 'INVARCHECK: inv |= prop...OK')) and
        not re.search(r'(?im)\b(error|failed|invalid invariant|exception)\b',text)):
        return 'proved_safety_query_only'
    if execution['returncode']==0 and statuses==['sat']:
        return 'counterexample_in_query_model'
    return 'unknown_or_error'


def solve(directory, pono, timeout):
    execution = run_command([pono,*ENGINE,str(directory/'model.btor2')],directory/'pono.log',timeout)
    text = (directory/'pono.log').read_text()
    result = {'execution':execution,'status':classify(execution,text)}
    if result['status']=='counterexample_in_query_model':
        result['counterexample_witness_available']=False
        result['counterexample_scope']='Engine reports SAT; installed MBIC3 witness extraction is not implemented'
    return result


TINY = {
 'constrained_even_nonzero_init': ('proved_safety_query_only', '''module Tiny(input clk, input [3:0] step);
reg [3:0] q = 4'd10;
always @* assume(step == 0 || step == 2);
always @(posedge clk) q <= q + step;
always @* assert(q[0] == 0);
endmodule
'''),
 'nonzero_initial_value_negative': ('counterexample_in_query_model', '''module Tiny(input clk);
reg [3:0] q = 4'd10;
always @(posedge clk) q <= q;
always @* assert(q == 0);
endmodule
'''),
 'uninitialized_state_negative': ('counterexample_in_query_model', '''module Tiny(input clk);
reg [3:0] q;
always @(posedge clk) q <= q;
always @* assert(q == 0);
endmodule
'''),
 'symbolic_x_negative': ('counterexample_in_query_model', '''module Tiny(input clk);
wire [3:0] x = 4'bxxxx;
always @* assert(x == 0);
endmodule
'''),
 'changing_anyseq_negative': ('counterexample_in_query_model', '''module Tiny(input clk);
reg [3:0] q = 0;
(* anyseq *) reg [3:0] arbitrary_value;
always @(posedge clk) q <= arbitrary_value;
always @* assert(q[0] == 0);
endmodule
'''),
 'initial_reset_and_repeated_reset': ('proved_safety_query_only', '''module Tiny(input clk,rst_n,input [3:0] step);
reg [3:0] q;
always @* begin
 if ($initstate) assume(!rst_n);
 assume(step == 0 || step == 2);
 if (rst_n) assert(q[0] == 0);
end
always @(posedge clk) if(!rst_n) q <= 6; else q <= q + step;
endmodule
'''),
 'initial_reset_not_permanent_negative': ('counterexample_in_query_model', '''module Tiny(input clk,rst_n,input [3:0] step);
reg [3:0] q;
always @* begin
 if ($initstate) assume(!rst_n);
 assume(step == 0 || step == 2);
 if (rst_n) assert(q == 6);
end
always @(posedge clk) if(!rst_n) q <= 6; else q <= q + step;
endmodule
'''),
 'three_asserts_eight_constraints_positive': ('proved_safety_query_only', '''module Tiny(input clk,input [7:0] guarded);
reg [7:0] q = 8'ha5;
always @* begin
 assume(guarded[0] == 1); assume(guarded[1] == 0);
 assume(guarded[2] == 1); assume(guarded[3] == 0);
 assume(guarded[4] == 0); assume(guarded[5] == 1);
 assume(guarded[6] == 0); assume(guarded[7] == 1);
 assert(q[0] == 1); assert(q[1] == 0); assert(q == 8'ha5);
end
always @(posedge clk) q <= guarded;
endmodule
'''),
 'third_assertion_negative': ('counterexample_in_query_model', '''module Tiny(input clk,input [7:0] guarded);
reg [7:0] q = 8'ha5;
always @* begin
 assume(guarded[0] == 1); assume(guarded[1] == 0);
 assume(guarded[2] == 1); assume(guarded[3] == 0);
 assume(guarded[4] == 0); assume(guarded[5] == 1);
 assume(guarded[6] == 0); assume(guarded[7] == 1);
 assert(q[0] == 1); assert(q[1] == 0); assert(q == 0);
end
always @(posedge clk) q <= guarded;
endmodule
'''),
}


def validate_tiny(out, yosys, pono):
    records=[]
    for name,(expected,verilog) in TINY.items():
        d=out/name;d.mkdir();(d/'source.sv').write_text(verilog)
        script=f'read_verilog -formal -sv {yosys_path(d/"source.sv")}\n'+formal_prepare_command('Tiny')+formal_lower_command(yosys)
        script+='async2sync\ndffunmap\nsetundef -anyseq\n'
        script+=f'write_json {yosys_path(d/"prepared.json")}\n'
        prepare=checked_yosys(yosys,script,d,'prepare',30)
        counts=property_counts(read(d/'prepared.json'),'Tiny')
        require(counts['assert']==verilog.count('assert(') and counts['assume']==verilog.count('assume('),
                'Tiny frontend removed semantic properties')
        record={'name':name,'expected':expected,'source_sha256':digest(d/'source.sv'),'prepare':prepare,
            **export_btor(d/'prepared.json','Tiny',d,yosys,counts,30),**solve(d,pono,30)}
        (d/'summary.json').write_text(json.dumps(record,indent=2)+'\n')
        require(record['status']==expected,'Pono validation failed for '+name)
        if expected=='counterexample_in_query_model':
            bmc=run_command([pono,'-e','bmc','--smt-solver','btor','--witness','-k','6',
                str(d/'model.btor2')],d/'negative_bmc.log',30)
            text=(d/'negative_bmc.log').read_text()
            require(not bmc['timeout'] and bmc['returncode']==0 and
                re.findall(r'(?m)^(sat|unsat|unknown|error)$',text)==['sat'], 'Negative BMC did not confirm SAT')
            match=re.search(r'(?ms)^sat\n.*?^\.\s*$',text)
            require(match is not None,'Negative BMC lacks a complete witness')
            (d/'counterexample.wit').write_text(match.group(0).rstrip()+'\n')
            checked=run_command([str(Path(pono).with_name('btorsim')),'-c',str(d/'model.btor2'),
                str(d/'counterexample.wit')],d/'witness_check.log',30)
            require(not checked['timeout'] and checked['returncode']==0,'Independent negative witness check failed')
            record['negative_bmc']=bmc;record['witness_check']=checked
            record['witness_sha256']=digest(d/'counterexample.wit')
            (d/'summary.json').write_text(json.dumps(record,indent=2)+'\n')
        records.append(record)
    return records


def collect_dependencies(source):
    info=read(source/'summary.json')
    require(info['status']=='prepared_query_only' and info['abstraction_mode']=='alu_mul', 'Wrong authoritative query')
    require(info['query_property_counts']=={'assert':3,'assume':8,'cover':0},'Wrong authoritative property set')
    known={'source.json':'source_json_sha256','core.json':'core_json_sha256','core.v':'core_sha256',
        'AdmissionScreen.sv':'harness_sha256','formal_screen.py':'script_sha256','abstract_datapath.py':'abstraction_helper_sha256',
        'program_rom.py':'rom_helper_sha256','program.hex':'rom_image_sha256','temporal.py':'temporal_helper_sha256'}
    deps={}
    for name,key in known.items():
        require(digest(source/name)==info[key],'Prepared source changed: '+name)
        deps[str(source/name)]=info[key]
    for label in ('native_word_domain_import','external_rom_domain_import'):
        for name,expected in info[label]['proof_dependencies_sha256'].items():
            require(digest(Path(name))==expected,'Proof dependency changed: '+name)
            deps[name]=expected
    require(digest(Path(info['query_core_path']))==info['query_core_sha256'],'Prepared query core changed')
    deps[info['query_core_path']]=info['query_core_sha256']
    for name in ('summary.json','screen.json','prepare.ys','prepare.log'):
        deps[str(source/name)]=digest(source/name)
    require(digest(source/'prepare.log')==info['prepare']['log_sha256'] and info['prepare']['returncode']==0,
        'Prepared model export did not complete')
    return info,deps


def verify_dependencies(deps):
    for name,expected in deps.items():
        require(digest(Path(name))==expected,'Dependency changed during word-level run: '+name)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source',type=Path)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--evidence',type=Path,required=True)
    ap.add_argument('--validation',type=Path,help='Previously completed validation summary; recheck every dependency')
    ap.add_argument('--yosys',default=str(OSS/'yosys'));ap.add_argument('--pono',default=str(OSS/'pono'))
    args=ap.parse_args();out=args.output.resolve();out.mkdir(parents=True,exist_ok=False)
    evidence=args.evidence.resolve();evidence.mkdir(parents=True,exist_ok=False)
    runner_sha=digest(Path(__file__));backend_sha=digest(Path(temporal.__file__))
    (out/'word_solver.py').write_bytes(Path(__file__).read_bytes());(out/'temporal.py').write_bytes(Path(temporal.__file__).read_bytes())
    if args.validation:
        validation=read(args.validation);require(validation['status']=='tiny_semantics_validated','Tiny validation did not pass')
        require(validation['runner_sha256']==runner_sha and validation['backend_sha256']==backend_sha,'Validation source changed')
        verify_dependencies(validation['dependencies'])
        records=validation['tiny_tests']
    else:
        records=validate_tiny(out,args.yosys,args.pono)
    record={'status':'tiny_semantics_validated','accepted_optimization':False,'runner_sha256':runner_sha,
        'backend_sha256':backend_sha,'engine_arguments':ENGINE,'tiny_tests':records,'dependencies':{}}
    if args.source:
        source=args.source.resolve();info,deps=collect_dependencies(source)
        deps[str(Path(__file__).resolve())]=runner_sha;deps[str(Path(temporal.__file__).resolve())]=backend_sha
        for executable in (args.yosys,args.pono):deps[str(Path(executable).resolve())]=digest(Path(executable))
        if args.validation:
            deps[str(args.validation.resolve())]=digest(args.validation)
            deps.update(validation['dependencies'])
        record['prepared_query_summary_sha256']=digest(source/'summary.json')
        record['original_query_property_counts']=info['query_property_counts']
        d=out/'target';d.mkdir()
        record['target_export']=export_btor(source/'screen.json','AdmissionScreen',d,args.yosys,info['query_property_counts'],120)
        verify_dependencies(deps)
        record['target']=solve(d,args.pono,120)
        verify_dependencies(deps)
        record['status']=record['target']['status'];record['dependencies']=deps
    else:
        record['dependencies']={str(p):digest(p) for p in out.rglob('*') if p.is_file()}
        for executable in (args.yosys,args.pono):record['dependencies'][str(Path(executable).resolve())]=digest(Path(executable))
    require(digest(Path(__file__))==runner_sha and digest(Path(temporal.__file__))==backend_sha,'Runner/backend changed')
    (out/'summary.json').write_text(json.dumps(record,indent=2)+'\n')
    for p in out.rglob('*'):
        if p.is_file() and not (args.source and p.parent.name=='target' and p.name in ('exported.json','model.btor2','model.info','model.ywb')):
            dst=evidence/p.relative_to(out);dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dst)
    (evidence/'SHA256SUMS').write_text(''.join(f'{digest(p)}  {p.relative_to(evidence)}\n' for p in sorted(evidence.rglob('*')) if p.is_file() and p.name!='SHA256SUMS'))
    print(json.dumps({'status':record['status'],'accepted_optimization':False,'tiny_tests':len(records)}))


if __name__=='__main__':main()
