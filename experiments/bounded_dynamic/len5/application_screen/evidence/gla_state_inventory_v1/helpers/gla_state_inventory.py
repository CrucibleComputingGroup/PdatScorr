#!/usr/bin/env python3
"""Map retained GLA state to source FF drivers; no solver is invoked."""
import argparse
from collections import Counter,defaultdict
import hashlib
import json
from pathlib import Path
import re
import struct

from gate_resume import aig_parts
from gate_solver import digest,require


def read_aig(path):
    data=Path(path).read_bytes();cursor=data.index(b'\n')+1;words=data[:cursor].split()
    require(words[0]==b'aig','Expected binary AIG');values=list(map(int,words[1:]));values += [0]*(9-len(values))
    maximum,inputs,latches,outputs,ands,bads,constraints,justice,fairness=values
    require(not justice and not fairness,'Fairness ordering is unsupported')
    def line():
        nonlocal cursor
        stop=data.index(b'\n',cursor);value=data[cursor:stop];cursor=stop+1;return value
    latch_lines=[tuple(map(int,line().split())) for _ in range(latches)]
    observations=[int(line()) for _ in range(outputs+bads+constraints)]
    def varint():
        nonlocal cursor
        result=0;shift=0
        while True:
            byte=data[cursor];cursor+=1;result|=(byte&127)<<shift
            if not byte&128:return result
            shift+=7;require(shift<=35,'Malformed AIG delta')
    nodes=[]
    for variable in range(inputs+latches+1,maximum+1):
        first=2*variable-varint();second=first-varint();nodes.append((first,second))
    require(len(nodes)==ands,'Malformed AIG node count')
    return {'header':values,'latches':latch_lines,'nodes':nodes,'observations':observations}


def transition_binding(source,folded):
    """Exact shared structural hashing; never infer correspondence by names."""
    require(source['header'][1]==folded['header'][1] and folded['header'][2]==source['header'][2]+1,
            'Expected same inputs and exactly one added constraint-history FF')
    intern={};next_id=1
    def atom(key):
        nonlocal next_id
        if key not in intern:intern[key]=next_id*2;next_id+=1
        return intern[key]
    def conjunction(a,b):
        if a==0 or b==0 or a==(b^1):return 0
        if a==1:return b
        if b==1 or a==b:return a
        return atom(('and',min(a,b),max(a,b)))
    def signatures(model):
        _,inputs,latches,_,_,*_=model['header'];v=[0]
        v += [atom(('input',i)) for i in range(inputs)]
        v += [atom(('state',i)) for i in range(latches)]
        def literal(x):return v[x>>1]^(x&1)
        for a,b in model['nodes']:v.append(conjunction(literal(a),literal(b)))
        return [literal(row[0]) for row in model['latches']]
    before=signatures(source);after=signatures(folded)
    mismatch=[i for i,x in enumerate(before) if x!=after[i]]
    init_match=all((a[1] if len(a)>1 else 0)==(b[1] if len(b)>1 else 0) for a,b in zip(source['latches'],folded['latches']))
    return {'existing_latches':len(before),'checked_existing_next_state_cones':len(before),'mismatched_indices':mismatch,
        'all_existing_initial_values_match':init_match,'established':not mismatch and init_match,
        'method':'Shared hash-consed AND DAGs with exact PI/state-index labels, complement edges, and elementary AND constant/idempotence rules; no SAT/random simulation.'}


def group_name(driver):
    if '$flatten\\dut.$driver$' not in driver:return 'external_environment' if '$flatten\\dut.' not in driver else 'other_native'
    name=driver.split('$driver$',1)[1]
    for token,group in [('.u_rob.','ROB'),('.u_alu_unit.u_arith_rs.','ALU_RS'),('.u_int_regstat.','register_scoreboard'),
        ('.u_int_rf.','integer_RF'),('.u_issue_stage.u_issue_fifo.','issue_queue'),('.u_issue_stage.','issue_register_control'),
        ('u_fetch_stage.u_pc_gen.','PC'),('u_fetch_stage.u_mem_if.','IFU_buffers_control'),
        ('u_fetch_stage.','IFU_predictor'),('.u_branch_unit.','branch_unit'),('.u_load_store_unit.','load_store_unit'),
        ('.gen_mult_unit.','MUL_unit'),('.gen_div_unit.','DIV_unit')]:
        if token in name:return group
    return 'other_native'


def source_owners(model,vmap):
    drivers={}
    for name,cell in model['cells'].items():
        for port,direction in cell['port_directions'].items():
            if direction=='output':
                for index,bit in enumerate(cell['connections'][port]):
                    if type(bit)is int:
                        require(bit not in drivers,'Ambiguous model driver');drivers[bit]=(name,port,index)
    owners=defaultdict(dict);unresolved=defaultdict(list)
    for line in Path(vmap).read_text().splitlines():
        words=line.split(' ',3)
        if words[0]!='latch':continue
        latch,offset,name=int(words[1]),int(words[2]),words[3]
        require(name in model['netnames'],'Exported latch alias missing from prepared model')
        net=model['netnames'][name];require(not net.get('upto',0),'Ascending native alias indexing requires separate audit')
        index=offset-net.get('offset',0);require(0<=index<len(net['bits']),'Exported alias offset out of range')
        bit=net['bits'][index];route=[]
        while type(bit)is int and bit in drivers:
            driver,port,position=drivers[bit];cell=model['cells'][driver]
            if cell['type']=='$dff' and port=='Q':
                key=(driver,position)
                owners[latch][key]={'driver':driver,'bit':position,'group':group_name(driver),
                    'source_attribute':cell.get('attributes',{}).get('src'),
                    'alias':name,'alias_offset':offset,'route':route}
                break
            # Ownership only: preserve the distinction between reset-masked
            # visible outputs and raw native state. This establishes no Q=Y theorem.
            if cell['type']=='$mux' and port=='Y' and len(cell['connections']['S'])==1:
                aa,bb=cell['connections']['A'][position],cell['connections']['B'][position]
                candidates=[x for x in (aa,bb) if type(x)is int]
                if len(candidates)==1 and len(route)<2:
                    route.append({'cell':driver,'kind':'reset_constant_mux_owner_lineage','output_bit':bit,'state_input_bit':candidates[0]})
                    bit=candidates[0];continue
            unresolved[latch].append({'alias':name,'offset':offset,'driver':driver,'type':cell['type']});break
    return owners,unresolved


def inventory(prepared,vmap,folded,maps):
    source_path=prepared/'screen.aig';source=read_aig(source_path);fold=read_aig(folded)
    binding=transition_binding(source,fold);require(binding['established'],'Source/folded latch ordering not established')
    model=json.loads((prepared/'screen.json').read_text())['modules']['AdmissionScreen']
    owners,unresolved=source_owners(model,vmap);all_rows=[];summary={};kept_by_map={}
    reference_graph,_=aig_parts(folded)
    for label,path in maps.items():
        graph,ext=aig_parts(path);require(graph==reference_graph,'Gate map original graph differs')
        require('g'in ext,'Missing GLA gate classes')
        classes=struct.unpack('<'+'i'*(len(ext['g'])//4),ext['g'])
        _,inputs,latches,_,ands,*_=fold['header']
        selected=[i for i in range(latches) if classes[1+inputs+i]];kept_by_map[label]=set(selected)
        groups=Counter();fields=Counter();rows=[]
        for index in selected:
            records=list(owners[index].values())
            if index==source['header'][2]:group='folded_constraint_history'
            elif not records and index==source['header'][2]-1 and source['latches'][index]==(1,):group='export_initialization_tracker'
            elif len(records)==1:group=records[0]['group']
            else:group='unresolved' if not records else 'merged_native_owners'
            groups[group]+=1
            if len(records)==1:fields[records[0]['driver']]+=1
            row={'map':label,'folded_latch':index,'source_latch':index if index<source['header'][2] else None,
                'group':group,'owners':records,'unresolved_aliases':unresolved.get(index,[])}
            rows.append(row);all_rows.append(row)
        # Attribute retained combinational gate cones to the next-state inputs
        # of retained FF groups. These counts overlap and are not area estimates.
        names=sorted(groups);mask_by_group={n:1<<i for i,n in enumerate(names)};masks=[0]*(fold['header'][0]+1)
        for row in rows:masks[fold['latches'][row['folded_latch']][0]>>1]|=mask_by_group[row['group']]
        first=inputs+latches+1
        for var in range(fold['header'][0],first-1,-1):
            if masks[var]:
                a,b=fold['nodes'][var-first];masks[a>>1]|=masks[var];masks[b>>1]|=masks[var]
        cones={n:sum(bool(classes[var]) and bool(masks[var]&bit) for var in range(first,fold['header'][0]+1)) for n,bit in mask_by_group.items()}
        summary[label]={'map_path':str(path),'map_sha256':digest(path),'retained_latches':len(selected),
            'retained_AND_objects':sum(bool(classes[i]) for i in range(first,first+ands)),
            'state_groups':dict(groups),'largest_driver_fields':[{'driver':n,'bits':count} for n,count in fields.most_common(35)],
            'retained_AND_fanin_by_FF_group_overlapping':cones,'unresolved_retained_latches':[r['folded_latch'] for r in rows if r['group']=='unresolved']}
    deltas={}
    labels=list(maps)
    for old,new in zip(labels,labels[1:]):
        added=kept_by_map[new]-kept_by_map[old];removed=kept_by_map[old]-kept_by_map[new]
        added_rows=[r for r in all_rows if r['map']==new and r['folded_latch'] in added]
        deltas[old+'->'+new]={'added_latches':sorted(added),'removed_latches':sorted(removed),
            'added_state_groups':dict(Counter(r['group'] for r in added_rows))}
    return {'status':'source_bound_retained_state_inventory','source_aig_sha256':digest(source_path),
        'prepared_model_sha256':digest(prepared/'screen.json'),'vmap_sha256':digest(vmap),'folded_sha256':digest(folded),
        'latch_order_binding':binding,'maps':summary,'deltas':deltas,'retained_state_rows':all_rows,
        'limitations':'Inventory only, no solver or new theorem. Raw async2sync state and visible reset-mux aliases are distinguished by recorded ownership routes; this mapping authorizes no state substitution. Gate-cone counts overlap and are not physical area. Export initialization and folded constraint-history state are not native hardware.'}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--prepared',type=Path,required=True)
    p.add_argument('--vmap',type=Path,required=True);p.add_argument('--folded',type=Path,required=True)
    p.add_argument('--map',action='append',required=True,help='label=absolute_map_path');p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();maps={k:Path(v).resolve() for k,v in (x.split('=',1) for x in a.map)}
    require(not a.output.exists(),'Fresh report path required')
    report=inventory(a.prepared.resolve(),a.vmap.resolve(),a.folded.resolve(),maps)
    report['script_sha256']=digest(Path(__file__));a.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v['state_groups'] for k,v in report['maps'].items()},indent=2))


if __name__=='__main__':main()
