#!/usr/bin/env python3
"""Hash-check and compare frozen gap1/gap2 Harvard traces; no simulation."""
import argparse
import csv
import json
from pathlib import Path
import re
import shutil

from run_gap1_ablation import admitted_rows,read,require,sha,timing


def audit(directory,gap):
    for line in (directory/'SHA256SUMS').read_text().splitlines():
        expected,name=line.split('  ',1);require(sha(directory/name)==expected,'Evidence hash mismatch: '+name)
    host=read(directory/'summary.json');manifest=read(directory/'simulator_manifest.json')
    require(host['status']=='passed' and host['program_exit_ok'] and host['all_64_output_stores_and_exit_checked'],'Unqualified run')
    require(manifest['instruction_min_accept_spacing']==gap,'Wrong external acceptance setting')
    stores=list(csv.DictReader((directory/'accepted_stores.csv').open()))
    rows=[{k:int(v) for k,v in r.items()} for r in csv.DictReader((directory/'platform_edges.csv').open())]
    exit_time=int(stores[-1]['time']);require(int(stores[-1]['data_store_addr_o'])==0x20000100,'Exit store missing')
    exit_cycle=next(r['cycle'] for r in rows if r['time']==exit_time)
    full,_,_=timing(rows,gap);through_exit,_,_=timing([r for r in rows if r['cycle']<=exit_cycle],gap)
    recorded=host.get('memory_timing_full_trace',host.get('memory_timing'))
    require(json.loads(json.dumps(full))==recorded,'Recomputed timing disagrees with recorded result')
    admissions=admitted_rows(directory/'occupancy.csv',exit_cycle)
    faults=through_exit['fetch_faults'];zero_fault_payloads=all(r['fetch_response_word']==0 for r in rows if r['reset_n'] and r['fetch_exception'])
    require(zero_fault_payloads,'Fault returned nonzero instruction payload')
    return {'evidence_path':str(directory),'summary_sha256':sha(directory/'summary.json'),
        'hash_manifest_sha256':sha(directory/'SHA256SUMS'),'reported_cpu_cycles':int(re.search(r'total CPU cycles:\s+(\d+)',(directory/'run.log').read_text()).group(1)),
        'exit_store_monitor_cycle':exit_cycle,'all64_outputs_and_exit0':True,
        'admissions_through_exit':admissions,'timing_full_trace':full,'timing_through_exit':through_exit,
        'all_observed_instruction_fault_payloads_zero':zero_fault_payloads,
        'first_completed_instruction_fault_monitor_cycle':min((f['response_cycle'] for f in faults),default=None),
        'actual_alu_issue_inversion_count':host['out_of_order']['actual_alu_issue_inversion_count'],
        'stores':[{k:int(v) for k,v in r.items() if k!='time'} for r in stores]}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--gap1',type=Path,required=True)
    p.add_argument('--gap2',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();out=a.output.resolve();out.mkdir(parents=True,exist_ok=False)
    first,second=audit(a.gap1.resolve(),1),audit(a.gap2.resolve(),2)
    require(first.pop('stores')==second.pop('stores'),'Architectural stores differ')
    image_hashes={}
    for name in ('program.elf','instruction.hex','data.hex'):
        require(sha(a.gap1/name)==sha(a.gap2/name),'Image mismatch: '+name);image_hashes[name]=sha(a.gap1/name)
    native_facts=read(a.gap1/'summary.json')
    for key in ('native_core_and_capacities_unchanged','all_74_core_source_hashes_match',
                'top_testbench_diff_is_only_gate_and_passive_observer','memory_implementation_byte_identical'):
        require(native_facts[key],'Unmatched native platform: '+key)
    witnesses=[{'row':i,**first['admissions_through_exit']['first_admission_by_index'][str(i)]}
        for i in first['admissions_through_exit']['indices'] if i<4]
    first_fault=first['first_completed_instruction_fault_monitor_cycle']
    require(all(first_fault is None or int(w['cycle_pre_edge'])<first_fault for w in witnesses),'Admission witness occurs only after fault')
    record={'status':'matched_finite_ablation_audited','gap1':first,'gap2':second,
        'identical_image_sha256':image_hashes,'identical_64_results_and_exit_store':True,
        'original_core_capacity_and_memory_implementation_matched':True,
        'row_0_through_3_admission_witnesses':witnesses,'witnesses_precede_first_completed_instruction_fault':True,
        'sampling':'Native pre-update values at actual rising edges. cycle_pre_edge and exit_store_monitor_cycle use the monitor counter; reported CPU cycles use the upstream host reporting interval. Fetch latency ends at accepted response, so includes native response backpressure.',
        'interpretation':'Gap1 concretely disproves the no-admission property for rows1,2,3 on this exact program/platform. Row0 was not observed admitted. Gap2 absence in this finite run is not a universal proof. No hardware optimization, software speedup, or area claim.',
        'source_sha256':sha(Path(__file__).resolve())}
    (out/'comparison.json').write_text(json.dumps(record,indent=2)+'\n');shutil.copyfile(Path(__file__),out/'audit_source.py')
    (out/'SHA256SUMS').write_text(''.join(f'{sha(f)}  {f.name}\n' for f in sorted(out.iterdir()) if f.is_file()))
    print(json.dumps({'status':record['status'],'gap1_indices':first['admissions_through_exit']['indices'],
        'gap2_indices':second['admissions_through_exit']['indices'],'gap1_cycles':first['reported_cpu_cycles'],
        'gap2_cycles':second['reported_cpu_cycles']}))


if __name__=='__main__':main()
