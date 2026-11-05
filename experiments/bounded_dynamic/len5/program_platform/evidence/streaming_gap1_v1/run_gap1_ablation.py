#!/usr/bin/env python3
"""Matched finite Harvard gap1 run using frozen gap2 ELF/ROM/data bytes."""
import argparse
import csv
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE.parent),str(HERE.parent/'application_screen')]
from prepare_frontend import digest,PRE_FPU_PIN
from analyze_fetch_spacing import native_edges,timing,dynamic_issue
from run_div_falsifier import extract
from run_streaming import stores
from run_platform import INPUT,MASK,csv_write


def read(path):return json.loads(path.read_text())
def sha(path):return digest(path.read_bytes())
def require(value,message):
    if not value:raise ValueError(message)


def admitted_rows(path,exit_cycle=None):
    rows=list(csv.DictReader(path.open()))
    if exit_cycle is not None:rows=[r for r in rows if int(r['cycle_pre_edge'])<=exit_cycle]
    allocated={int(r['new_idx']) for r in rows if int(r['insert'])}
    first={str(i):next(r for r in rows if int(r['insert']) and int(r['new_idx'])==i) for i in sorted(allocated)}
    return {'indices':sorted(allocated),'first_admission_by_index':first,
        'max_live_pre_edge':max(int(r['live_pre']) for r in rows),
        'max_live_post_edge':max(int(r['live_post']) for r in rows),
        'rows_0_through_3_all_admitted':set(range(4))<=allocated,
        'any_row_0_through_3_admitted':bool(set(range(4))&allocated)}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--simulator-build',required=True,type=Path)
    ap.add_argument('--gap2-evidence',required=True,type=Path)
    ap.add_argument('--gap2-build',required=True,type=Path)
    ap.add_argument('--output',required=True,type=Path);ap.add_argument('--evidence',required=True,type=Path)
    args=ap.parse_args();build=args.simulator_build.resolve();paired=args.gap2_evidence.resolve()
    gap2build=args.gap2_build.resolve();out=args.output.resolve();evidence=args.evidence.resolve()
    out.mkdir(parents=True,exist_ok=False);evidence.mkdir(parents=True,exist_ok=False)
    manifest=read(build/'manifest.json');reference=read(paired/'simulator_manifest.json');positive=read(paired/'summary.json')
    require(manifest['build_returncode']==0 and manifest['upstream_commit']==PRE_FPU_PIN,'Build failed/wrong native source')
    require(manifest['instruction_min_accept_spacing']==1 and reference['instruction_min_accept_spacing']==2,'Not gap1/gap2 pair')
    require(positive['status']=='passed' and positive['all_64_output_stores_and_exit_checked'] and positive['program_exit_ok'],'Gap2 reference unqualified')
    require(not manifest['core_rtl_source_edits'] and not reference['core_rtl_source_edits'],'Core RTL was edited')
    for key in ('core_source_sha256','capacity_parameters','fetch_fifo_depth','memory_pipe_num','boot_pc',
                'instruction_memory_platform','harvard_source_sha256','qualification_monitor_sha256'):
        require(manifest[key]==reference[key],'Unmatched platform/core setting: '+key)
    require(manifest['memory_pipe_num']==manifest['fetch_fifo_depth']==2,'Wrong fixed memory/FIFO configuration')
    require(manifest['instruction_memory_platform']=='separate_immutable_elf_executable_rom','Not Harvard platform')
    for relative,expected in manifest['core_source_sha256'].items():
        require(sha(build/relative)==sha(gap2build/relative)==expected,'Changed native core source: '+relative)
    for relative,expected in reference['testbench_prepared_sha256'].items():
        require(sha(gap2build/'source'/relative)==expected,'Changed reference testbench source')
        require(sha(build/'source'/relative)==manifest['testbench_prepared_sha256'][relative],'Changed gap1 testbench source')
        if relative!='tb/tb_bare.sv':require(manifest['testbench_prepared_sha256'][relative]==expected,'Unmatched memory/host/reset implementation')
    # Check the entire top-level TB differs solely by the qualified external gate
    # and its passive observer. No response/flush/reset logic may change.
    expected=(gap2build/'source/tb/tb_bare.sv').read_bytes()
    for old,new in [(b'.instr_valid_i             (qualification_instr_memory_valid)',b'.instr_valid_i             (dp2mem_instr_valid)'),
                    (b'.instr_ready_o             (qualification_instr_memory_ready)',b'.instr_ready_o             (mem2dp_instr_ready)'),
                    (b'localparam int unsigned InstrMinAcceptSpacing = 2;\n`include "instruction_spacing_gate.svh"\n`include "platform_monitor.svh"\n',b'')]:
        require(expected.count(old)==1,'Reference gap2 gate structure changed');expected=expected.replace(old,new)
    require(expected==(build/'source/tb/tb_bare.sv').read_bytes(),'Additional top-level testbench differences')
    for line in (paired/'SHA256SUMS').read_text().splitlines():
        expected,name=line.split('  ',1);require(sha(paired/name)==expected,'Changed frozen gap2 evidence: '+name)
    for name in ('program.elf','instruction.hex','data.hex','elf_image_manifest.json','streaming.S','platform.ld','input.bin'):
        shutil.copyfile(paired/name,out/name)
    require(sha(out/'instruction.hex')==positive['elf_images']['instruction_hex_sha256'] and
            sha(out/'data.hex')==positive['elf_images']['data_hex_sha256'],'Program bytes not exactly paired')
    binary=build/'obj_dir/Vtb_bare';require(sha(binary)==manifest['binary_sha256'],'Simulator binary changed')
    source_files=[Path(__file__).resolve(),HERE/'run_platform.py',HERE.parent/'qualify_simulation.py',
                  HERE.parent/'run_div_falsifier.py',HERE.parent/'application_screen/run_streaming.py',
                  HERE.parent/'application_screen/analyze_fetch_spacing.py']
    sources={str(p):sha(p) for p in source_files}
    command=[str(binary),'+firmware='+str(out/'data.hex'),'+instruction_rom='+str(out/'instruction.hex'),
             '--max_cycles=10000','--dump_waves=true','--dump_trace=true','--log_level=LOG_LOW']
    with (out/'run.log').open('w') as log:
        run=subprocess.run(command,cwd=out,env={**os.environ,'PATH':'/usr/bin:/bin:/usr/local/bin'},stdout=log,stderr=subprocess.STDOUT,timeout=60)
    log=(out/'run.log').read_text();exit_ok=run.returncode==0 and 'Program exit with code: 0x00 (SUCCESS)' in log and 'Simulation completed successfully' in log and not any(t in log.lower() for t in ('error','failure','timeout'))
    subprocess.run(['/usr/bin/fst2vcd',str(out/'logs/waves.fst'),'-o',str(out/'all.vcd')],check=True,capture_output=True)
    occupancy=extract(out/'all.vcd',evidence/'rs_state.vcd',evidence/'occupancy.csv')
    writes=stores(out/'all.vcd');expected=[{'data_store_addr_o':0x2000+i*8,'data_store_wdata_o':(x+1)&MASK,'data_store_be_o':255} for i,x in enumerate(INPUT)]
    expected.append({'data_store_addr_o':0x20000100,'data_store_wdata_o':0,'data_store_be_o':1})
    stores_ok=[{k:v for k,v in row.items() if k!='time'} for row in writes]==expected
    rows=native_edges(out/'all.vcd',{'fetch_response_word':'TOP.tb_bare.u_datapath.instr_rdata_i'})
    service,fetches,loads=timing(rows,1);issue=dynamic_issue(out/'logs/qualification_events.csv')
    words={int(x['word'],16) for x in positive['elf_images']['instruction_words']}|{0}
    require(all(r['fetch_response_word'] in words for r in rows if r['reset_n']),'Active payload outside frozen ROM/fault domain')
    require(all(r['fetch_response_word']==0 for r in rows if r['reset_n'] and r['fetch_exception']),'Nonzero fault payload')
    exit_cycle=next(r['cycle'] for r in rows if r['time']==writes[-1]['time']) if stores_ok else None
    execution,_,_=timing([r for r in rows if r['cycle']<=exit_cycle],1) if exit_cycle is not None else ({},[],[])
    admissions=admitted_rows(evidence/'occupancy.csv',exit_cycle);paired_admissions=admitted_rows(paired/'occupancy.csv')
    for name,data in [('accepted_stores.csv',writes),('platform_edges.csv',rows),('fetch_responses.csv',fetches),('load_responses.csv',loads)]:csv_write(evidence/name,data)
    for name in ('qualification_events.csv','sim-trace.log'):shutil.copyfile(out/'logs'/name,evidence/name)
    for p in out.iterdir():
        if p.is_file() and p.name!='all.vcd':shutil.copyfile(p,evidence/p.name)
    for p in source_files:require(sha(p)==sources[str(p)],'Analysis source changed');shutil.copyfile(p,evidence/p.name)
    shutil.copyfile(build/'manifest.json',evidence/'simulator_manifest.json')
    shutil.copyfile(paired/'summary.json',evidence/'gap2_summary.json')
    shutil.copyfile(paired/'simulator_manifest.json',evidence/'gap2_simulator_manifest.json')
    shutil.copyfile(paired/'occupancy.csv',evidence/'gap2_occupancy.csv')
    shutil.copyfile(gap2build/'source/LICENSE',evidence/'LICENSE.LEN5') if (gap2build/'source/LICENSE').exists() else None
    cpu=lambda text:int(re.search(r'total CPU cycles:\s+(\d+)',text).group(1))
    summary={'status':'passed' if exit_ok and stores_ok and issue['witness_found'] else 'failed',
        'classification':'Finite matched external fetch-spacing ablation; not a universal occupancy theorem or accepted optimization',
        'program_exit_ok':exit_ok,'all_64_output_stores_and_exit_checked':stores_ok,'accepted_stores':len(writes),
        'returncode':run.returncode,'run_command':command,'reported_cpu_cycles':cpu(log),'exit_store_cycle':exit_cycle,
        'native_core_and_capacities_unchanged':True,'all_74_core_source_hashes_match':len(manifest['core_source_sha256'])==74,
        'top_testbench_diff_is_only_gate_and_passive_observer':True,'memory_implementation_byte_identical':True,
        'elf_rom_and_data_bytes_identical':True,'source_sha256':sources,'simulator_manifest_sha256':sha(build/'manifest.json'),
        'raw_fst_sha256':sha(out/'logs/waves.fst'),'raw_vcd_sha256':sha(out/'all.vcd'),
        'memory_timing_full_trace':service,'memory_timing_through_exit':execution,'out_of_order':issue,
        'occupancy':occupancy,'admissions_through_exit':admissions,'all_active_instruction_payloads_in_elf_words_or_zero':True,
        'gap2_comparison':{'evidence_path':str(paired),'summary_sha256':sha(paired/'summary.json'),
            'simulator_manifest_sha256':sha(paired/'simulator_manifest.json'),'reported_cpu_cycles':cpu((paired/'run.log').read_text()),
            'occupancy':paired_admissions,'memory_timing_full_trace':positive['memory_timing']},
        'raw_run_path':str(out),'build_path':str(build),
        'limitation':'The 1-cycle and 2-cycle gaps describe two external platforms. Cycle difference is not software optimization overhead. A native row admission is a finite counterexample to its universal no-admission property for gap1; lack of an admission in gap2 is finite evidence only.'}
    (evidence/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    (evidence/'SHA256SUMS').write_text(''.join(f'{sha(p)}  {p.name}\n' for p in sorted(evidence.iterdir()) if p.is_file() and p.name!='SHA256SUMS'))
    print(json.dumps({k:summary[k] for k in ['status','reported_cpu_cycles','exit_store_cycle','admissions_through_exit']}))
    return 0 if summary['status']=='passed' else 1


if __name__=='__main__':raise SystemExit(main())
