#!/usr/bin/env python3
"""Prove original Scheduler/SelectLogic no-FP state and requests after reset.

The dispatch-event contract includes wrong-path writes. This does not prove
that an arbitrary binary, predecode predicate, or full core meets that contract.
"""
import hashlib
import json
from pathlib import Path
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SRC = ROOT/'rsd/Processor/Src'
BIN = ROOT.parent.parent/'tools/oss-cad-suite-20261104/oss-cad-suite/bin'
DEFINES = ['RSD_SYNTHESIS','RSD_SYNTHESIS_DESIGN_COMPILER','REF=input',
           'RSD_DISABLE_DEBUG_REGISTER','RSD_DISABLE_PERFORMANCE_COUNTER',
           'RSD_MARCH_INT_ISSUE_WIDTH=2','RSD_MARCH_FP_PIPE','RSD_ENABLE_ZBA','RSD_ENABLE_ZICOND']

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    out = HERE/'results/scheduler_nofp'
    out.mkdir(parents=True, exist_ok=True)
    common = (HERE/'rtl_sources.txt').read_text().splitlines()[:18]
    relatives = common + ['Scheduler/SchedulerIF.sv','Scheduler/WakeupSelectIF.sv',
        'Recovery/RecoveryManagerIF.sv','MulDivUnit/MulDivUnitIF.sv',
        'FloatingPointUnit/FPDivSqrtUnitIF.sv','Debug/DebugIF.sv',
        'Primitives/Picker.sv','Scheduler/Scheduler.sv','Scheduler/SelectLogic.sv']
    sources = [SRC/r for r in relatives]
    (HERE/'scheduler_sources.txt').write_text('\n'.join(relatives)+'\n')
    executions = []
    def run(name, command):
        start = time.monotonic()
        p = subprocess.run(command, text=True, capture_output=True, timeout=180)
        log = p.stdout+p.stderr
        (out/(name+'.log')).write_text(log)
        executions.append(dict(name=name, command=command, returncode=p.returncode,
                               seconds=time.monotonic()-start))
        return p.returncode, log
    for mode, extra in [('contract',['PSCORR_NO_FP_CONTRACT']),('negative',[])]:
        smt = out/(mode+'.smt2')
        script = out/(mode+'.ys')
        script.write_text(' '.join(['read_slang','--single-unit','--top','SchedulerNoFPProof',
            '-I'+str(SRC),*['-D'+s for s in DEFINES+extra],*[str(p) for p in sources],
            str(HERE/'SchedulerNoFPProof.sv')])+'\nprep -top SchedulerNoFPProof -flatten\n'
            'memory_map\nopt_clean\ndffunmap\nchformal -lower\nwrite_smt2 -wires '+str(smt)+'\n')
        rc, log = run(mode+'_elaborate',[str(BIN/'yosys'),'-m','slang','-s',str(script)])
        if rc: raise RuntimeError(mode+' elaboration failed')
        model=smt.read_text()
        counts={k:model.count('; yosys-smt2-'+k+' ') for k in ('assert','assume','cover')}
        expected=dict(assert_=35, assume=3 if mode=='contract' else 1, cover=1)
        assert counts=={'assert':expected['assert_'],'assume':expected['assume'],'cover':1}, counts
        commands=[('base',[]),('induction',['-i']),('cover',['-c'])] if mode=='contract' else [('counterexample',[])]
        for label, flags in commands:
            cmd=[str(BIN/'yosys-smtbmc'),'-s','z3','-t','6',*flags]
            if mode=='negative':cmd+=['--dump-vcd',str(out/'negative.vcd')]
            rc, log=run(mode+'_'+label,cmd+[str(smt)])
            if mode=='contract' and (rc or 'Status: PASSED' not in log):raise RuntimeError(label+' failed')
            if mode=='negative' and (rc==0 or 'Status: FAILED' not in log):raise RuntimeError('Negative control did not expose a counterexample')
    summary=dict(status='passed', scope='Actual original Scheduler and SelectLogic, reset base plus temporal induction; no full-core equivalence/application-contract proof',
        contract='After initial reset, every actual scheduler.write lane has opType != MOP_TYPE_FP; no validity/retirement filter',
        properties=dict(assertions=35, assumptions=3, covers=1),
        source_sha256={r:sha(SRC/r) for r in relatives},harness_sha256=sha(HERE/'SchedulerNoFPProof.sv'),
        executions=executions,negative_control='Removing the dispatch contract yields a reached FP-request/grant counterexample')
    (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print('PASS: 35 actual-RTL properties; base, induction, mixed-class cover; no-contract counterexample')

if __name__=='__main__':main()
