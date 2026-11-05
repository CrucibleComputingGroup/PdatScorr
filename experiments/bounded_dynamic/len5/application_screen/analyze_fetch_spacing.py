#!/usr/bin/env python3
"""Audit actual native memory edges and dynamic issue in a finite LEN5 run."""
from __future__ import annotations
import argparse
from collections import Counter, deque
import csv
import json
from pathlib import Path
import re
import shutil
import sys

sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from prepare_frontend import digest


def native_edges(vcd):
    dp='TOP.tb_bare.u_datapath.'
    names={'cycle':'TOP.tb_bare.curr_cycle','clk':'TOP.tb_bare.clk_i',
           'reset_n':'TOP.tb_bare.rst_ni','flush':dp+'mem_flush_o',
           'core_req':dp+'instr_req_o','core_gnt':dp+'instr_gnt_i',
           'memory_req':'TOP.tb_bare.u_memory_bare_emu.instr_valid_i',
           'memory_gnt':'TOP.tb_bare.u_memory_bare_emu.instr_ready_o'}
    for key,port in {
        'fetch_addr':'instr_addr_o','fetch_response_valid':'instr_rvalid_i',
        'fetch_response_ready':'instr_rready_o','fetch_exception':'instr_except_raised_i',
        'fetch_exception_code':'instr_except_code_i','load_req':'data_load_req_o',
        'load_gnt':'data_load_gnt_i','load_addr':'data_load_addr_o','load_tag':'data_load_tag_o',
        'load_response_valid':'data_load_rvalid_i','load_response_ready':'data_load_rready_o',
        'load_response_tag':'data_load_tag_i','load_response_data':'data_load_rdata_i',
        'load_exception':'data_load_except_raised_i','load_exception_code':'data_load_except_code_i',
    }.items(): names[key]=dp+port
    codes,scopes,values,previous,rows={},[],{},{},[]
    time=0
    def number(key,state):
        raw=state.get(codes[key],'x')
        return None if any(c in raw.lower() for c in 'xz') else int(raw,2)
    def flush():
        nonlocal previous
        if number('clk',values)==1 and number('clk',previous)==0:
            row={key:number(key,previous) for key in names if key!='clk'}
            if row['reset_n']==1:
                assert None not in row.values(), 'Unknown active native interface value'
            rows.append({'time':time,**row})
        previous=dict(values)
    with vcd.open() as source:
        for line in source:
            words=line.split()
            if words and words[0]=='$scope':scopes.append(words[2])
            elif words and words[0]=='$upscope':scopes.pop()
            elif words and words[0]=='$var':
                full='.'.join(scopes+[words[4]])
                for key,wanted in names.items():
                    if full==wanted:codes[key]=words[3]
            if words and words[0]=='$enddefinitions':break
        assert codes.keys()==names.keys(), names.keys()-codes.keys()
        used=set(codes.values())
        for line in source:
            line=line.rstrip()
            if line.startswith('#'):flush();time=int(line[1:])
            elif line.startswith(('b','B')):
                value,code=line[1:].split()
                if code in used:values[code]=value
            elif line and line[0] in '01xXzZ' and line[1:] in used:values[line[1:]]=line[0]
        flush()
    return rows


def timing(rows,minimum_spacing):
    fetch=deque();loads={};fetch_pairs=[];load_pairs=[];canceled=[];accepts=[];gaps=[]
    last_accept=None;max_fetch=0;max_load=0;flush_edges=[]
    for row in rows:
        cycle=row['cycle']
        if not row['reset_n']:
            fetch.clear();loads.clear();last_accept=None
            continue
        accepted=bool(row['core_req'] and row['core_gnt'])
        assert accepted==bool(row['memory_req'] and row['memory_gnt']),row
        if row['fetch_response_valid'] and row['fetch_response_ready']:
            assert fetch, f'Unmatched fetch response at {cycle}'
            request=fetch.popleft()
            fetch_pairs.append({**request,'response_cycle':cycle,
                                'latency':cycle-request['request_cycle'],
                                'response_on_flush':row['flush'],
                                'exception':row['fetch_exception'],'exception_code':row['fetch_exception_code']})
        if row['flush']:
            flush_edges.append(cycle)
            canceled.extend({**request,'flush_cycle':cycle} for request in fetch)
            fetch.clear()
        if accepted:
            if last_accept is not None:gaps.append(cycle-last_accept)
            last_accept=cycle;accepts.append(cycle)
            request={'request_cycle':cycle,'address':row['fetch_addr']}
            if row['flush']:canceled.append({**request,'flush_cycle':cycle})
            else:fetch.append(request)
        # The upstream memory model flushes only instruction traffic. Data
        # responses remain tracked across a core misprediction/flush.
        if row['load_response_valid'] and row['load_response_ready']:
            tag=row['load_response_tag'];assert tag in loads, f'Unmatched data response at {cycle}'
            request=loads.pop(tag)
            load_pairs.append({**request,'response_cycle':cycle,'latency':cycle-request['request_cycle'],
                               'data':row['load_response_data'],'exception':row['load_exception'],
                               'exception_code':row['load_exception_code']})
        if row['load_req'] and row['load_gnt']:
            tag=row['load_tag'];assert tag not in loads, f'Reused outstanding load tag at {cycle}'
            loads[tag]={'request_cycle':cycle,'tag':tag,'address':row['load_addr']}
        max_fetch=max(max_fetch,len(fetch));max_load=max(max_load,len(loads))
    assert gaps and min(gaps)>=minimum_spacing
    assert all(p['latency']>0 for p in fetch_pairs+load_pairs)
    result={'accepted_fetch_count':len(accepts),'accepted_fetch_gap_histogram':dict(Counter(gaps)),
            'minimum_accepted_fetch_gap':min(gaps),'maximum_fetch_outstanding_after_edge':max_fetch,
            'complete_fetch_response_count':len(fetch_pairs),
            'fetch_latency_histogram':dict(Counter(p['latency'] for p in fetch_pairs)),
            'fetch_faults':[p for p in fetch_pairs if p['exception']],
            'flush_cycles':flush_edges,'fetch_cancellations':canceled,'fetch_pending_at_end':list(fetch),
            'complete_load_response_count':len(load_pairs),'maximum_load_outstanding_after_edge':max_load,
            'load_latency_histogram':dict(Counter(p['latency'] for p in load_pairs)),
            'load_faults':[p for p in load_pairs if p['exception']],
            'load_pending_at_end':list(loads.values()),'endpoint_acceptance_equal_at_all_active_edges':True}
    return result,fetch_pairs,load_pairs


def dynamic_issue(events):
    records=[];active={};requests={};epoch=0
    for row in csv.DictReader(events.open()):
        kind=row['event'];cycle=int(row['cycle']);rob=int(row['rob'])
        if kind in ('RESET','FLUSH'):
            active.clear();epoch+=1
            if kind=='RESET':requests.clear()
        elif kind=='DISPATCH':
            item={'sequence':len(records),'epoch':epoch,'dispatch_cycle':cycle,'rob':rob,
                  'pc':int(row['v0'],16),'instruction':int(row['v1'],16)}
            records.append(item);active[rob]=item
        elif kind in ('ALU_START','ALU_RESULT'):
            assert rob in active
            active[rob][kind.lower()+'_cycle']=cycle
            if kind=='ALU_RESULT':active[rob]['result']=int(row['v0'],16)
        elif kind=='LOAD_REQUEST':
            assert rob in active
            item=active[rob];tag=int(row['v0'],16);assert tag not in requests
            item.update(request_cycle=cycle,memory_tag=tag,address=int(row['v1'],16));requests[tag]=item
        elif kind=='LOAD_RESPONSE':
            tag=int(row['v0'],16);assert tag in requests
            requests.pop(tag).update(response_cycle=cycle,load_value=int(row['v1'],16))
    inversions=[]
    for index,older in enumerate(records):
        if 'alu_start_cycle' not in older:continue
        for younger in records[index+1:]:
            if (younger['epoch']==older['epoch'] and 'alu_start_cycle' in younger
                    and older['dispatch_cycle']<younger['dispatch_cycle']
                    and younger['alu_start_cycle']<older['alu_start_cycle']):
                pair={'older_alu':older,'younger_alu':younger}
                if index and records[index-1]['instruction']&127==3:
                    load=records[index-1]
                    if ((older['instruction']>>15)&31)==((load['instruction']>>7)&31):
                        pair['older_load_dependency']=load
                inversions.append(pair)
    return {'witness_found':bool(inversions),'actual_alu_issue_inversion_count':len(inversions),
            'first_witness':inversions[0] if inversions else None,
            'scope':'Actual ALU execution handshakes within one reset/flush epoch; finite trace only'}


def write_csv(path,rows):
    assert rows
    with path.open('w') as out:
        writer=csv.DictWriter(out,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--simulator-build',type=Path,required=True)
    parser.add_argument('--run',type=Path,required=True)
    parser.add_argument('--evidence',type=Path,required=True)
    args=parser.parse_args()
    build,run,evidence=args.simulator_build.resolve(),args.run.resolve(),args.evidence.resolve()
    output=evidence/'platform_timing_summary.json';assert not output.exists()
    manifest=json.loads((build/'manifest.json').read_text())
    host=json.loads((evidence/'summary.json').read_text())
    assert host['all_64_output_stores_and_exit_checked'] and host['program_exit_ok']
    assert host['simulator_manifest_sha256']==digest((build/'manifest.json').read_bytes())
    assert manifest['core_rtl_source_edits'] is False and manifest['fetch_fifo_depth']==2
    rows=native_edges(run/'all.vcd')
    minimum=manifest.get('instruction_min_accept_spacing',1)
    summary,fetch,loads=timing(rows,minimum)
    store_rows=list(csv.DictReader((evidence/'accepted_stores.csv').open()))
    exit_time=int(store_rows[-1]['time'])
    assert int(store_rows[-1]['data_store_addr_o'])==0x20000100
    exit_cycle=next(r['cycle'] for r in rows if r['time']==exit_time)
    execution,_,_=timing([r for r in rows if r['cycle']<=exit_cycle],minimum)
    source_monitor=run/'logs/platform_edges.csv'
    monitor_audit=None
    if source_monitor.exists():
        monitored={int(r['cycle']):r for r in csv.DictReader(source_monitor.open())}
        hex_fields={'fetch_addr','load_addr','load_tag','load_response_tag'}
        for row in rows:
            saved=monitored[row['cycle']]
            for key,value in saved.items():
                assert row[key]==int(value,16 if key in hex_fields else 10),(row['cycle'],key)
        monitor_audit={'matching_vcd_edges':len(rows),'monitor_edges':len(monitored),
                       'sha256':digest(source_monitor.read_bytes())}
        destination=evidence/'logs/platform_edges.csv'
        if destination.exists():assert destination.read_bytes()==source_monitor.read_bytes()
        else:shutil.copyfile(source_monitor,destination)
    occupancy=list(csv.DictReader((evidence/'occupancy.csv').open()))
    witness=dynamic_issue(evidence/'logs/qualification_events.csv')
    write_csv(evidence/'native_platform_edges.csv',rows)
    write_csv(evidence/'fetch_response_intervals.csv',fetch)
    write_csv(evidence/'load_response_intervals.csv',loads)
    summary={'scope':'Finite unchanged-core external-platform screen; no invariant or optimization proof',
             'sampling':'Pre-update values at actual rising clock edges; latency=response-edge minus accepted-request-edge. Returned fetches paired FIFO; flush-canceled and end-pending intervals reported separately.',
             'minimum_platform_fetch_accept_spacing':minimum,'full_trace':summary,
             'through_exit_store':execution,'exit_store_cycle':exit_cycle,
             'reported_cpu_cycles':int(re.search(r'total CPU cycles:\s+(\d+)',(run/'run.log').read_text()).group(1)),
             'monitored_last_cycle':rows[-1]['cycle'],'monitor_vcd_crosscheck':monitor_audit,
             'used_alu_allocation_indices':sorted({int(r['new_idx']) for r in occupancy if r['insert']=='1'}),
             'max_alu_live_pre_edge':max(int(r['live_pre']) for r in occupancy),
             'max_alu_live_post_edge':max(int(r['live_post']) for r in occupancy),
             'dynamic_issue':witness,'all_64_output_stores_and_exit_checked':True,
             'capacities':manifest['capacity_parameters'],'fetch_fifo_depth':manifest['fetch_fifo_depth'],
             'memory_pipe_num':manifest['memory_pipe_num'],'core_rtl_source_edits':False,
             'simulator_manifest_sha256':digest((build/'manifest.json').read_bytes()),
             'program_source_sha256':digest((run/'program.S').read_bytes()),
             'raw_fst_sha256':digest((run/'logs/waves.fst').read_bytes()),
             'raw_vcd_sha256':digest((run/'all.vcd').read_bytes()),
             'analyzer_sha256':digest(Path(__file__).read_bytes()),
             'artifact_sha256':{name:digest((evidence/name).read_bytes()) for name in
                               ('native_platform_edges.csv','fetch_response_intervals.csv','load_response_intervals.csv')}}
    output.write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({k:summary[k] for k in ('reported_cpu_cycles','used_alu_allocation_indices',
          'max_alu_live_post_edge','exit_store_cycle')}))
    print(json.dumps({'fetch_latency':summary['full_trace']['fetch_latency_histogram'],
                      'load_latency':summary['full_trace']['load_latency_histogram'],
                      'load_faults':summary['full_trace']['load_faults'],'ooo':witness['witness_found']}))


if __name__=='__main__':main()
