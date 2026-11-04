#!/usr/bin/env python3
"""Actual RTL tag-ODC proof with explicit bounded read service and negatives."""
import argparse, hashlib, json, os, shutil, signal, subprocess, time
from pathlib import Path

HERE=Path(__file__).resolve().parent

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('baseline',type=Path);p.add_argument('output',type=Path)
    p.add_argument('--toolbin',type=Path,required=True)
    p.add_argument('--spacing',type=int,default=3);p.add_argument('--latency',type=int,default=5)
    p.add_argument('--unordered',action='store_true')
    p.add_argument('--negative',action='store_true')
    p.add_argument('--depth',type=int,default=16)
    p.add_argument('--cover-depth',type=int,default=20)
    args=p.parse_args();base=args.baseline.resolve();out=args.output.resolve()
    if out.exists():raise SystemExit('Refusing existing proof output')
    out.mkdir(parents=True)
    # Preserve exactly the environment used by this run, including when the
    # working-tree monitor is edited for a later, separately named experiment.
    monitor=out/'ReadServiceContract.sv'
    shutil.copy2(HERE/'ReadServiceContract.sv',monitor)
    ports=json.loads((base/'baseline.json').read_text())['modules']['MshrObserved']['ports']
    declarations=[f'input logic [{len(port["bits"])-1}:0] {name}' for name,port in ports.items() if port['direction']=='input']
    lines=['import CacheSystemTypes::*;','module MshrTimingProof('+',\n'.join(declarations)+');']
    for name,port in ports.items():
        if port['direction']=='input':continue
        lines.append(f'logic [{len(port["bits"])-1}:0] {name};')
    lines+=['MshrObserved dut(.*);',
        f'ReadServiceContract #(.MIN_SPACING({args.spacing}),.MAX_LATENCY({args.latency}),.ORDERED({0 if args.unordered else 1})) service(.*);',
        'logic [1:0] accepted, returned; logic seen_three;',
        'always_ff @(posedge clk) begin',
        '  if (rst) begin accepted<=0; returned<=0; seen_three<=0; end',
        '  else begin',
        '    if(read_accept) accepted<=accepted+1\'b1;',
        '    if(response_valid) returned<=returned+1\'b1;',
        '    if(read_accept && allocated_id==3) seen_three<=1;',
        '  end','end',
        'wire [1:0] saved0=dut.handler.mshr[0].memSerial;',
        'wire [1:0] saved1=dut.handler.mshr[1].memSerial;',
        'wire waiting0=dut.handler.mshr[0].phase==MSHR_PHASE_MISS_READ_MEM_RECEIVE;',
        'wire waiting1=dut.handler.mshr[1].phase==MSHR_PHASE_MISS_READ_MEM_RECEIVE;',
        'logic pending0,pending1;',
        'always_comb begin',
        '  pending0=0; pending1=0;',
        '  for(integer j=0;j<4;j++) if(j<service.count) begin',
        '    pending0 |= saved0==service.queue_id[j];',
        '    pending1 |= saved1==service.queue_id[j];',
        '  end','end',
        'always_comb if(!rst) begin',
        '  assert(!waiting0 || !response_valid || saved0[0]!=response_id[0] || saved0[1]==response_id[1]);',
        '  assert(!waiting1 || !response_valid || saved1[0]!=response_id[0] || saved1[1]==response_id[1]);']
    if not args.negative:
        lines+=['  assert(service.count<=2);',
                '  assert(allocated_id==accepted);',
                '  assert(dut.ids.headPtr==accepted);',
                '  assert(dut.ids.tailPtr==returned);',
                '  assert((accepted-returned)==service.count[1:0]);',
                '  assert(({1\'b0,dut.ids.pointer.regCount}+service.count)==4);',
                '  assert(!waiting0 || pending0);',
                '  assert(!waiting1 || pending1);']
        for j in range(4):
            lines.append(f'  assert(dut.ids.freeList[{j}]==2\'d{j});')
            lines.append(f'  if({j}<service.count) assert(service.queue_id[{j}]==(returned+2\'d{j}));')
    lines+=['  cover(service.count==2 && waiting0 && waiting1);',
        '  cover(waiting0 && response_valid && saved0[1]!=response_id[1]);',
        '  cover(waiting1 && response_valid && saved1[1]!=response_id[1]);',
        '  cover(seen_three && read_accept && allocated_id==0);',
        'end','endmodule']
    harness=out/'MshrTimingProof.sv';harness.write_text('\n'.join(lines)+'\n')
    front=(base/'baseline.ys').read_text().splitlines()[0].replace('--top MshrObserved','--top MshrTimingProof')
    front+=' '+str(monitor)+' '+str(harness)
    smt=out/'model.smt2';ys=out/'proof.ys'
    ys.write_text(front+'\nprep -top MshrTimingProof -flatten\nmemory_map\nopt_clean\ndffunmap\nchformal -lower\nwrite_smt2 -wires '+str(smt)+'\n')
    records=[]
    def run(name,command):
        started=time.monotonic()
        proc=subprocess.Popen(command,text=True,stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT,start_new_session=True)
        try:
            log,_=proc.communicate(timeout=180);rc=proc.returncode
        except subprocess.TimeoutExpired:
            # SMTBMC owns a solver child: terminate the whole task-local group.
            os.killpg(proc.pid,signal.SIGTERM)
            try:log,_=proc.communicate(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid,signal.SIGKILL)
                log,_=proc.communicate()
            rc=124
        (out/(name+'.log')).write_text(log)
        records.append(dict(name=name,command=command,returncode=rc,seconds=time.monotonic()-started))
        print(name,rc,flush=True)
        return rc,log
    rc,_=run('elaborate',[str(args.toolbin.resolve()/'yosys'),'-m','slang','-s',str(ys)])
    status='failed'
    if rc==0:
        stages=[('negative',[])] if args.negative else [('base',[]),('induction',['-i']),('cover',['-c'])]
        passed=True
        for name,flags in stages:
            depth=args.cover_depth if name=='cover' else args.depth
            trace=name+('_%' if name=='cover' else '')+'.vcd'
            rc,log=run(name,[str(args.toolbin.resolve()/'yosys-smtbmc'),'-s','z3','--noprogress','-t',str(depth),*flags,'--dump-vcd',str(out/trace),str(smt)])
            ok=(rc==1 and 'Status: FAILED' in log and 'Assert failed in MshrTimingProof:' in log and (out/trace).exists()) if args.negative else (rc==0 and 'Status: PASSED' in log)
            passed &= ok
            if not ok:break
        if passed:status='negative_witness' if args.negative else 'passed'
    result=dict(status=status,scope='Actual original RSD MSHR/FreeList component; not full-core equivalence or application adherence',
        contract=dict(min_spacing=args.spacing,max_latency=args.latency,ordered=not args.unordered),
        source_manifest=str(base/'manifest.json'),
        source_manifest_sha256=hashlib.sha256((base/'manifest.json').read_bytes()).hexdigest(),
        baseline_json_sha256=hashlib.sha256((base/'baseline.json').read_bytes()).hexdigest(),
        harness_sha256=hashlib.sha256(harness.read_bytes()).hexdigest(),
        service_contract_sha256=hashlib.sha256(monitor.read_bytes()).hexdigest(),
        model_sha256=hashlib.sha256(smt.read_bytes()).hexdigest() if smt.exists() else None,
        tool_sha256={name:hashlib.sha256((args.toolbin/name).read_bytes()).hexdigest() for name in ['yosys','yosys-smtbmc','z3']},
        executions=records)
    (out/'summary.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
    if status=='failed':raise SystemExit(1)

if __name__=='__main__':main()
