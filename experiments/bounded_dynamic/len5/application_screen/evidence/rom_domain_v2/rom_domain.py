#!/usr/bin/env python3
"""Prove the exact generated Harvard producer's external instruction domain.

The original ObservedCore instance is cut at every output. The ROM and pipeline
are copied verbatim; no PC sequence, request rule, or core readiness is assumed.
Positive base+induction uses proved stage helpers. Negative controls require an
actual failing external response, not just a failed helper invariant.
"""
from __future__ import annotations
import argparse
import difflib
import importlib.util
import json
from pathlib import Path
import re
import shutil
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[3]))
from odc.temporal import checked_yosys, digest, formal_prepare_command, formal_lower_command, proof_passed, run_command, validate_single_clock, yosys_path
import odc.temporal as temporal


def domain(signal, words):
    return '(' + ' || '.join(f"{signal} == 32'h{x:08x}" for x in sorted(set(words) | {0})) + ')'


def extract_producer(source, ports, words, helpers):
    assert source.count('module AdmissionScreen(') == 1 and source.count('endmodule') == 1
    header_end = source.index(');') + 2
    header, body = source[:header_end], source[header_end:]
    cut = {n:len(p['bits']) for n,p in ports.items() if p['direction']=='output'}
    assert {'instr_addr_o','instr_req_o','instr_rready_o','mem_flush_o'} <= cut.keys()
    extra = [f'input wire [{w-1}:0] {n}' for n,w in cut.items()]
    extra += ['output wire observed_valid', 'output wire [31:0] observed_word',
              'output wire observed_fault', 'output wire [4:0] observed_code']
    header = header.replace('module AdmissionScreen(', 'module RomDomain(', 1)
    header = header[:-2] + ',\n  ' + ',\n  '.join(extra) + ');'
    removed = []
    dut = re.findall(r'^  ObservedCore dut\(.*\);\n', body, re.M)
    assert len(dut)==1
    body=body.replace(dut[0],'');removed.append(dut[0])
    for n,w in cut.items():
        declaration=f'  wire [{w-1}:0] {n};\n'
        assert body.count(declaration)==1
        body=body.replace(declaration,'');removed.append(declaration)
    assertions=re.findall(r'^    assert \(.*\);\n',body,re.M)
    assert len(assertions)==3 and len(re.findall(r'\bassert\s*\(',body))==3
    assert any('probe_insert' in line for line in assertions)
    assert any('data_load_rvalid_i' in line for line in assertions)
    assert any('data_store_rvalid_i' in line for line in assertions)
    for line in assertions:body=body.replace(line,'');removed.append(line)
    assert body.count('assume (!rst_ni);')==1 and len(re.findall(r'\bassume\s*\(',body))==1
    added=['  assign observed_valid = instr_rvalid_i;', '  assign observed_word = instr_rdata_i;',
           '  assign observed_fault = instr_except_raised_i;', '  assign observed_code = instr_except_code_i;',
           '  always @* if (rst_ni) begin',
           '    assert (!observed_valid || '+domain('observed_word',words)+');']
    if helpers:
        assert 'reg [1:0] iv, ifault; reg [31:0] ins0, ins1;' in source
        added += ['    assert (!iv[0] || '+domain('ins0',words)+');',
                  '    assert (!iv[1] || '+domain('ins1',words)+');']
    added += ['  end','']
    body=body.replace('endmodule','\n'.join(added)+'endmodule')
    result=header+body
    return result, {'arbitrary_core_output_ports':cut,'removed_original_assertions':assertions,
        'removed_core_instance_and_wire_declarations':[x for x in removed if x not in assertions],
        'retained_external_assumptions':['if ($initstate) assume (!rst_ni)'],
        'helper_assertions_added':2 if helpers else 0,'internal_assumptions_added':0,
        'initial_pipeline_state':'Unconstrained native synchronous-reset registers; no initialization added',
        'all_remaining_original_producer_source_preserved_verbatim':True}


def witness_rows(path):
    scopes,codes,values,rows=[],{},{},[]
    wanted={'rst_ni','observed_valid','observed_word','observed_fault','observed_code',
            'instr_addr_o','instr_req_o','instr_rready_o','mem_flush_o','smt_step'}
    current_time=None
    sampled_word=False
    for line in path.read_text().splitlines():
        p=line.split()
        if p and p[0]=='$scope':scopes.append(p[2])
        elif p and p[0]=='$upscope':scopes.pop()
        elif p and p[0]=='$var' and p[4] in wanted:
            codes[p[3]]=p[4]
        elif line.startswith('#'):
            if current_time is not None and sampled_word and 'smt_step' in values:
                rows.append({'vcd_time':current_time,**values})
            current_time=int(line[1:])
            sampled_word=False
        elif line.startswith('b'):
            bitstring,code=line[1:].split()
            if code in codes:
                assert set(bitstring)<={'0','1'}
                values[codes[code]]=int(bitstring,2)
                sampled_word |= codes[code]=='observed_word'
        elif line and line[0] in '01' and line[1:] in codes:values[codes[line[1:]]]=int(line[0])
    if current_time is not None and sampled_word and 'smt_step' in values:
        rows.append({'vcd_time':current_time,**values})
    # SMTBMC emits full signal values for each real frame. Its trailing clock/step
    # marker contains no frame payload; carrying old values into it invents a frame.
    by_step={}
    for row in rows:by_step[row['smt_step']]=row
    return list(by_step.values())


def run_variant(name, source, ports, words, out, yosys, timeout, positive):
    directory=out/name;directory.mkdir()
    checker,extraction=extract_producer(source,ports,words,helpers=positive)
    (directory/'source_harness.sv').write_text(source)
    (directory/'RomDomain.sv').write_text(checker)
    (directory/'extraction.json').write_text(json.dumps(extraction,indent=2)+'\n')
    (directory/'extraction.diff').write_text(''.join(difflib.unified_diff(source.splitlines(True),checker.splitlines(True),fromfile='original_harness',tofile='producer_checker')))
    model=directory/'model.smt2'
    script=f'read_verilog -formal -sv {yosys_path(directory/"RomDomain.sv")}\n'+formal_prepare_command('RomDomain')+formal_lower_command(yosys)
    script+='async2sync\ndffunmap\nsetundef -anyseq\n'
    script+=f'write_json {yosys_path(directory/"model.json")}\nwrite_smt2 -wires {yosys_path(model)}\n'
    prepare=checked_yosys(yosys,script,directory,'prepare',timeout)
    design=json.loads((directory/'model.json').read_text());module=design['modules']['RomDomain']
    clocks=validate_single_clock(design,'RomDomain')
    counts={kind:sum(c['type']=='$'+kind for c in module['cells'].values()) for kind in ('assert','assume','cover')}
    assert counts=={'assert':3 if positive else 1,'assume':1,'cover':0}
    assert not any(b in ('x','z') for c in module['cells'].values() for bits in c['connections'].values() for b in bits)
    assert not any('init' in n.get('attributes',{}) for n in module['netnames'].values())
    command=[str(Path(yosys).with_name('yosys-smtbmc')),'-s','z3','-t','6','--noprogress']
    base=run_command(command+['--dump-vcd',str(directory/'counterexample.vcd'),str(model)],directory/'base.log',timeout)
    record={'name':name,'expected':'unbounded proof' if positive else 'external-response counterexample',
        'extraction':extraction,'prepare':prepare,'clock_model':clocks,'property_counts':counts,
        'source_harness_sha256':digest(directory/'source_harness.sv'),'checker_sha256':digest(directory/'RomDomain.sv'),
        'model_json_sha256':digest(directory/'model.json'),'smt_sha256':digest(model),'base':base}
    if positive:
        assert proof_passed(base),'Positive base did not prove'
        record['induction']=run_command(command+['-i',str(model)],directory/'induction.log',timeout)
        assert proof_passed(record['induction']),'Positive induction did not prove'
        record['status']='proved_unbounded'
    else:
        log=(directory/'base.log').read_text()
        assert not base['timeout'] and re.findall(r'Status:\s*(\w+)',log)==['FAILED'] and (directory/'counterexample.vcd').is_file()
        rows=witness_rows(directory/'counterexample.vcd')
        allowed=set(words)|{0}
        failing=[r for r in rows if r.get('rst_ni')==1 and r.get('observed_valid')==1 and r.get('observed_word') not in allowed]
        assert failing,'Negative witness does not violate the actual output predicate'
        (directory/'counterexample.json').write_text(json.dumps({'rows':rows,'failing_external_responses':failing},indent=2)+'\n')
        record.update(status='counterexample_observed',counterexample_sha256=digest(directory/'counterexample.vcd'),failing_external_responses=failing)
    (directory/'summary.json').write_text(json.dumps(record,indent=2)+'\n')
    return record


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--evidence',type=Path,required=True)
    ap.add_argument('--timeout',type=int,default=60)
    ap.add_argument('--yosys',default='/home/allenjin/Projects/DAC_pscorr/tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys')
    args=ap.parse_args();source,out,evidence=args.source.resolve(),args.output.resolve(),args.evidence.resolve()
    meta=json.loads((source/'summary.json').read_text())
    assert meta['instruction_model']=='immutable_rom' and meta['instruction_fault_payload']=='zero'
    for filename,key in [('AdmissionScreen.sv','harness_sha256'),('core.json','core_json_sha256'),('program.hex','rom_image_sha256'),('program_rom.py','rom_helper_sha256')]:
        assert digest(source/filename)==meta[key]
    ports=json.loads((source/'core.json').read_text())['modules']['datapath']['ports']
    original=(source/'AdmissionScreen.sv').read_text()
    spec=importlib.util.spec_from_file_location('frozen_program_rom',source/'program_rom.py')
    helper=importlib.util.module_from_spec(spec);spec.loader.exec_module(helper)
    rom=helper.read_image(source/'program.hex')
    assert rom['bytes']==56 and len(rom['words'])==14
    selector='\n'.join(helper.verilog_selector(rom,zero_fault_data=True))+'\n'
    assert original.count(selector)==1
    out.mkdir(parents=True,exist_ok=False);evidence.mkdir(parents=True,exist_ok=False)
    for name in ['AdmissionScreen.sv','program.hex','program_rom.py']:
        shutil.copyfile(source/name,out/name)
    shutil.copyfile(source/'summary.json',out/'source_summary.json')
    (out/'core_ports.json').write_text(json.dumps(ports,indent=2)+'\n')
    shutil.copyfile(__file__,out/'rom_domain.py')
    shutil.copyfile(temporal.__file__,out/'temporal_source.py')
    implementation_hash=digest(Path(temporal.__file__));runner_hash=digest(Path(__file__))
    words=list(rom['words'].values())
    records=[run_variant('positive',original,ports,words,out,args.yosys,args.timeout,True)]
    fault_selector='\n'.join(helper.verilog_selector(rom,zero_fault_data=False))+'\n'
    records.append(run_variant('arbitrary_fault_payload',original.replace(selector,fault_selector),ports,words,out,args.yosys,args.timeout,False))
    extra=out/'extra_word.hex'
    extra.write_text((source/'program.hex').read_text()+"@00000038\nEF BE AD DE\n")
    extra_rom=helper.read_image(extra)
    assert extra_rom['bytes']==60 and extra_rom['words'][56]==0xdeadbeef
    extra_selector='\n'.join(helper.verilog_selector(extra_rom,zero_fault_data=True))+'\n'
    records.append(run_variant('extra_rom_word',original.replace(selector,extra_selector),ports,words,out,args.yosys,args.timeout,False))
    assert digest(Path(temporal.__file__))==implementation_hash and digest(Path(__file__))==runner_hash
    record={'status':'proved_with_two_failing_negative_controls','accepted_hardware_optimization':False,
        'scope':'External instruction-response domain of the exact generated Harvard producer; arbitrary core outputs, unconstrained initial sync state, initial reset only',
        'conclusion':'For every unbounded trace, rst_ni && instr_rvalid_i implies the original14ROMwords or zero',
        'source_directory':str(source),'source_harness_sha256':meta['harness_sha256'],'core_port_descriptor_sha256':meta['core_json_sha256'],
        'core_ports_sha256':digest(out/'core_ports.json'),'source_summary_sha256':digest(out/'source_summary.json'),
        'rom_image_sha256':meta['rom_image_sha256'],'rom_helper_sha256':meta['rom_helper_sha256'],
        'runner_sha256':runner_hash,'safe_formal_backend_sha256':implementation_hash,
        'domain_words':[f'{x:08x}' for x in sorted(set(words)|{0})],
        'variants':records,'limits':'Does not prove core admission, data-domain/fault exclusion, or correctness of a replacement hardware design'}
    (out/'summary.json').write_text(json.dumps(record,indent=2)+'\n')
    for p in out.rglob('*'):
        if p.is_file() and p.name not in ('model.json',):
            dst=evidence/p.relative_to(out);dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dst)
    (evidence/'SHA256SUMS').write_text(''.join(f'{digest(p)}  {p.relative_to(evidence)}\n' for p in sorted(evidence.rglob('*')) if p.is_file() and p.name!='SHA256SUMS'))
    print(json.dumps({'status':record['status'],'variants':[{k:r[k] for k in ('name','status')} for r in records]}))


if __name__=='__main__':main()
