#!/usr/bin/env python3
"""Generate one proved scheduler request cut; retain all capacities and classes."""
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
SRC=HERE.parent/'rsd/Processor/Src'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    proof=HERE/'results/scheduler_nofp/summary.json'
    data=json.loads(proof.read_text())
    assert data['status']=='passed'
    for relative,digest in data['source_sha256'].items():
        assert sha(SRC/relative)==digest, 'Stale scheduler proof source: '+relative
    assert sha(HERE/'SchedulerNoFPProof.sv')==data['harness_sha256']
    source=SRC/'Scheduler/Scheduler.sv'
    original=source.read_text()
    old='''            wakeupSelect.fpIssueReq[i] = 
                notIssued[i] && isFP[i] && (!isFPDivSqrt[i] || (isFPDivSqrt[i] && canIssueFPDivSqrt));'''
    assert original.count(old)==1
    new='''            // Proven zero after reset under the no-FP actual-dispatch contract.
            wakeupSelect.fpIssueReq[i] = FALSE;'''
    target=HERE/'generated_scheduler_nofp'
    target.mkdir(exist_ok=True)
    candidate=target/'Scheduler.sv'
    candidate.write_text(original.replace(old,new))
    report={'contract':data['contract'],'scope':'One Scheduler FP-request vector cut, justified by actual original Scheduler+SelectLogic induction; not a full-core equivalence or application-domain proof',
        'capacity':'IQ16, ROB64 and all source parameters unchanged',
        'retained':'Integer, complex integer including mul/div, load/store scheduling, recovery and all payload RAMs',
        'removed_observation':'FP issue requests are constant zero; unobserved FP classification and availability logic may be eliminated by synthesis',
        'source_sha256':sha(source),'candidate_sha256':sha(candidate),
        'proof_summary':str(proof),'proof_summary_sha256':sha(proof),
        'harness_sha256':data['harness_sha256'],
        'limitations':['This does not itself remove the FP payload RAM or FP physical register file.',
                       'The no-FP contract is at every actual scheduler write, including wrong-path writes.',
                       'No proof establishes this contract from an arbitrary binary or just retired instructions.']}
    (target/'candidate_manifest.json').write_text(json.dumps(report,indent=2)+'\n')
    print(candidate)

if __name__=='__main__':main()
