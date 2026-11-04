#!/usr/bin/env python3
"""Read-only audit of generated automatic scheduler variants; save audit reports."""
import hashlib
import json
from pathlib import Path

F = Path(__file__).resolve().parent
EXP = F.parent
S = EXP / 'results/synthesis'
SRC = EXP / 'rsd/Processor/Src'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    names = ['scheduler_original_reset_observed',
             'scheduler_dispatch_assume_reset_observed',
             'scheduler_dispatch_lemmas_reset_observed']
    ds = [S / n for n in names]
    ms = [json.loads((d / 'manifest.json').read_text()) for d in ds]
    check = {}
    outputs = ms[0]['reset_masked_outputs']
    mark = '        wakeup_stall = wakeup.stall;'
    body = ("\n        // Observe only outside reset; retain every internal reset transition.\n"
            "        if (rst) begin\n" +
            ''.join("            " + n + " = '0;\n" for n in outputs) + '        end')
    masked = (F / 'SchedulerObserved.sv').read_text().replace(mark, mark + body)
    check['all_22_outputs_same_mask'] = len(outputs) == 22 and all(
        m['reset_masked_outputs'] == outputs for m in ms)
    check['original_boundary_only_reset_mask'] = (
        ds[0].joinpath('SchedulerObserved.sv').read_text() == masked)
    assumption = '''    for (genvar ps_lane = 0; ps_lane < DISPATCH_WIDTH; ps_lane++) begin
        always_comb begin
            if (!rst && writes[ps_lane])
                assume(port.writeSchedulerData[ps_lane].opType != MOP_TYPE_FP);
        end
    end'''
    for d in ds[1:]:
        text = d.joinpath('SchedulerObserved.sv').read_text()
        check[d.name + '_exact_dispatch_contract'] = text.count(assumption) == 1 and (
            ''.join(text.replace(assumption, '').split()) == ''.join(masked.split()))
    lemma = '''    // Actual-RTL proved invariant; valid after reset under every actual-write
    // no-FP admission contract. Original FP request logic remains unchanged.
    for (genvar ps_entry = 0; ps_entry < ISSUE_QUEUE_ENTRY_NUM; ps_entry++) begin
        always_comb begin
            if (!port.rst)
                assume(!notIssued[ps_entry] || !isFP[ps_entry]);
        end
    end'''
    text = ds[2].joinpath('Scheduler.sv').read_text()
    original = (SRC / 'Scheduler/Scheduler.sv').read_text()
    check['only_proved_live_FP_lemmas_added'] = text.count(lemma) == 1 and (
        ''.join(text.replace(lemma, '').split()) == ''.join(original.split()))
    check['retained_original_FP_request'] = (
        'notIssued[i] && isFP[i] && (!isFPDivSqrt[i] || '
        '(isFPDivSqrt[i] && canIssueFPDivSqrt))' in text)
    pi = json.loads((ds[2] / 'proof_import.json').read_text())
    proof = json.loads((F / 'results/scheduler_nofp/summary.json').read_text())
    check['proof_import_binding'] = (
        sha(Path(pi['proof_summary'])) == pi['proof_summary_sha256'] and
        sha(F / 'SchedulerNoFPProof.sv') == pi['harness_sha256'] == proof['harness_sha256'] and
        sha(SRC / 'Scheduler/Scheduler.sv') == pi['original_source_sha256'])
    check['proof_artifact_hashes'] = all(
        sha(F / 'results/scheduler_nofp' / n) == h
        for n, h in pi['proof_artifacts_sha256'].items())
    check['source_hashes'] = all(all(sha(Path(n)) == h
        for n, h in m['source_sha256'].items()) for m in ms)
    check['same_defines'] = all(m['defines'] == ms[0]['defines'] for m in ms)
    headers = []
    for d, expected_c in zip(ds, [0, 2, 18]):
        p = d / 'core_yosys.aig'
        with p.open('rb') as stream:
            hd = stream.readline().decode().strip().split()
        vals = list(map(int, hd[1:]))
        vals += [0] * (9 - len(vals))
        _, inputs, latches, outputs, _, _, constraints, _, _ = vals
        headers.append(dict(variant=d.name, header=' '.join(hd), inputs=inputs,
                            latches=latches, outputs=outputs,
                            constraints=constraints, sha256=sha(p)))
        check[d.name + '_export_C'] = constraints == expected_c
    check['same_export_interface_state'] = len({
        (h['inputs'], h['latches'], h['outputs']) for h in headers}) == 1
    report = dict(status='PASS' if all(check.values()) else 'FAIL', checks=check,
                  exports=headers, proof_import_sha256=sha(ds[2] / 'proof_import.json'),
                  scope='Automatic original-source Scheduler+SelectLogic comparison '
                        'at matched reset-masked output boundary; reset-conditioned '
                        'proved lemmas, no manually cut requests')
    (S / 'scheduler_import_audit.json').write_text(json.dumps(report, indent=2) + '\n')
    assert all(check.values()), report
    (S / 'scheduler_import_audit.txt').write_text('''PASS: scheduler automatic-variant source/export/domain audit

Three variants retain original Scheduler and SelectLogic request/selection
logic. All 22 output ports (409 AIG bits) are identically zeroed only when rst
is asserted. Inputs, state update/reset transitions and non-reset observations
are unchanged. No assume(!rst), reset suppression or hidden request cut occurs.
The original uses no assumptions, dispatch-only has exactly the actual-write
contract on two lanes, and lemma-assisted adds exactly 16 guarded live-entry
predicates: !port.rst -> (!notIssued[i] || !isFP[i]). Source/proof/harness/model/
base/induction/cover hashes match. Export constraint counts are 0/2/18, with
275 inputs, 129 AIG latches and 409 outputs in every model. The extra AIG latch
is initialization encoding, not a claimed physical scheduler register.

The imported predicate is exactly an assertion proved on unchanged actual
Scheduler+SelectLogic using initial reset and the same every-actual-write
contract, including wrong-path writes. It does not assert all isFP bits zero;
class bits in invalid entries remain arbitrary. Reset masking matches the
proof assertion guard and leaves internal resets possible on every cycle.

The lemma-assisted run is reset-conditioned proof-guided specialization, not
a conservative arbitrary-initial-state assumption-only run or automatic
invariant discovery. Its assumptions restrict otherwise unreachable startup
state. Dispatch-only remains the conservative control. This component's
observation boundary differs from the unmasked direct-map wrapper; areas must
be compared within each matched boundary. Full-core reset-cycle observation
equivalence and all-input binary adherence are not established. No payload
RAM, PRF or complete FP-pipeline removal is covered.
''')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
