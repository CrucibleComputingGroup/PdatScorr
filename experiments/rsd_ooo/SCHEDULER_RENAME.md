# Scheduler, reorder-buffer and rename experiments

These experiments retain the pinned complete RSD core, front-end/commit widths 2,
execution issue width 6, replay queue 20, LQ/SQ16, MSHR2 and upstream caches.
They distinguish capacity changes from a same-capacity proved scheduler cut.
All raw images, logs, traces and failure records remain under `results/`.

## Independent ROB/IQ capacity controls

`results/scheduler_sweep/parameter_audit.json` records source hashes and dependencies.
ROB64/32/16 are independently configurable. Admission requires occupancy at
most D-2. IQ admission requires at least 2 free entries and no free-list reset.
IQ's free list has 8 write ports (6 issued-entry releases plus 2 recovery returns),
so its RAM has 8 banks. IQ4 violates the entries/banks divisibility assertion.
IQ8 creates one-entry banks with reversed address slices and a zero-bit reset
counter. The unmodified controls therefore use IQ16/32/64. No execution-port
reduction or primitive repair is hidden in these controls.

Four new variants each run 8 upstream tests, 12 diagnostics and 2 applications:
88 new executions, plus 22 reused baseline executions. `summarize_scheduler_sweep.py`
checks case sets, input hashes, completion, outputs, source differences and timing.
The raw traces include initialization; their IQ occupancy maximum is not an
application-demand bound.

| Variant | CoreMark loop cycles / original | Dhrystone loop cycles / original |
| --- | ---: | ---: |
| ROB32, IQ16 | Did not complete | 1.001 |
| ROB16, IQ16 | 1.003 | 1.108 |
| ROB64, IQ32 | 1.116 | 1.059 |
| ROB64, IQ64 | 1.629 | 1.278 |

All 80 upstream/diagnostic architectural checks pass. Seven of 8 application
runs pass. ROB32 CoreMark reaches the 20,000,000-cycle limit without serial CRC
output. Its final committed PC is `0x1d0c`, the `mcycle` read in `stop_time`;
its last memory execution is at cycle 5,570,373. The final 100,000 resource samples
are identical: LQ13, SQ7, ROB0, IQ16, MSHR0, rename stalled, no allocation,
release or recovery. The commit watchdog prints repeatedly. This is observed
bounded noncompletion, not a universal claim about ROB32 or a certified result
for that application. No RTL repair removes the failure. See its
`noncompletion_audit.json`; no successful cycle ratio is assigned.

## Scheduler specialization under actual no-FP dispatch

The independent manually generated candidate
`formal/generated_scheduler_nofp/Scheduler.sv` ties only `fpIssueReq` to false.
Its component proof covers the pinned ROB64/IQ16/LQ16/SQ16/PRF64 instance under
every actual scheduler write having `opType != MOP_TYPE_FP`. All integer,
multiply/divide and memory operation classes remain permitted. The FP payload
RAM and physical register file are retained. This is not a whole-core proof.

`--fp-domain-trace` logs every actual scheduler write, including wrong-path
writes, through a typed accessor. It independently logs FP requests, issues,
replay entries, recorded entries and FP issue-pipeline valid bits. The 14
original/cut pairs (all 12 diagnostics and both applications) have zero FP events
and byte-identical serial, resource, memory, dispatch and FP-domain traces;
cycle and committed-instruction counters match exactly. CoreMark includes
RV32M and mutable-memory operations, beyond the earlier nonalias test domain.

The upstream `Asm/FP` control passes on the original at 4621 cycles. It has 45 FP
scheduler writes and 47 FP issues. The cut observes 15 FP scheduler writes outside
its contract, emits no FP issue requests and fails completion at the 100,000-cycle
limit. The failure remains explicit in `results/fp_scheduler/summary.json`.
`summarize_fp_scheduler.py` reproduces the paired audit. Candidate build guards
prevent silently transferring the pinned proof to different capacities.

The separate composition test combines the LSQ region cut and scheduler cut at
the same original capacities. All six stream inputs satisfy both contracts on
both cores and match in counters, output, and all four traces. This is six new
combined executions against six retained original executions, not a compositional
full-core proof. `results/combined_region_scheduler/summary.json` retains the
source/binary/input hashes and contract counts. Audit it with
`python3 experiments/rsd_ooo/summarize_combined.py`.

## Coupled physical-register controls

RSD asserts that integer and FP physical-register counts match. Its logical
register counts are 32 each. PRF32 has no rename free-list entries and produces
zero-width dimensions. PRF128/128 is a legal parameter growth control, with
96 free entries per class, unchanged execution ports, and derived tag/table widths.

PRF48/48 needs an explicitly labelled compatibility RTL change. The original
reset counter walks all 6-bit addresses, including 48..63. The guarded variant
disables those reset writes and clamps their inactive addresses to 0. The clamp
is needed because the LVT/XOR RAM reads write addresses even when write enable
is false. Only the integer/FP reset loops in `RegisterFile.sv` change; the counters
and reset protocol remain unchanged. The reset sweep still initializes all 48
valid registers. At 64/128 the guard is unreachable for the narrowed destination
address; `results/prf_guard/reset_guard_audit.json` records the bit-vector checks.

The matching guarded64 control retains exact original cycles and resource/memory
traces. Source and binary manifests separate pure PRF128 from guarded48/64.
Each runs 23 cases (8 upstream, 12 diagnostics, 2 applications, 1 FP control), for 69
new executions. All 69 reach completion with expected architectural outputs.

| PRF configuration, per class | CoreMark loop cycles | Dhrystone loop cycles |
| --- | ---: | ---: |
| Original64 | 3,336,042 | 255,757 |
| Guarded64 control | 3,336,042 | 255,757 |
| Guarded48 | 3,344,158 | 264,409 |
| Unmodified128 | 3,299,279 | 256,281 |

`rename_resources.csv` in the guarded48/64 runs records free INT/FP registers,
allocation/release counts, recovery and rename stalls. `results/prf_comparison.json`
and `.csv` retain exact results and qualifications. These capacity comparisons
are performance controls, not cycle-equivalent Pscorr transformations.

## Diagnostic qualifications and reproduction

Upstream RSD assertion macros print messages without terminating simulation.
`rsd_log_checks.py` derives literal/typed-format patterns from pinned source;
`results/rsd_named_assertion_catalog.json` records their provenance. CacheFlush
and Fence can trigger the existing 500-cycle progress watchdogs and subsequently
complete with expected outputs. Architectural completion is reported separately
from strict runner flags and named diagnostics. One empty-string assertion
cannot be identified retrospectively in old logs. No named non-watchdog failures
were found in the passing cases above.

Use fresh names and directories. `run_capacity_suite.py` retains every group
and continues after a group's failure; its nonzero return status must remain
visible. The commands below show one variant of each kind; the runner executes
the same 8+12+2 case suite for each binary.

```bash
python3 experiments/rsd_ooo/build_simulations.py --size 16 --rob-size 32 \
  --name new_rob32
python3 experiments/rsd_ooo/run_capacity_suite.py \
  --binary experiments/rsd_ooo/results/new_rob32/VMain_Zynq_Wrapper \
  --output experiments/rsd_ooo/results/new_scheduler/rob32_iq16

# Other independent settings: --rob-size 16; --issue-size 32; --issue-size 64.
python3 experiments/rsd_ooo/build_simulations.py --size 16 --prf-size 128 \
  --name new_prf128
python3 experiments/rsd_ooo/build_simulations.py --size 16 --prf-size 48 \
  --prf-reset-guard --rename-trace --name new_guard48
python3 experiments/rsd_ooo/build_simulations.py --size 16 --prf-size 64 \
  --prf-reset-guard --rename-trace --name new_guard64

# Same-capacity no-FP baseline/candidate; generated proof artifacts are required.
# The generator checks the retained passing proof and original-source hashes.
python3 experiments/rsd_ooo/formal/make_scheduler_nofp_candidate.py
python3 experiments/rsd_ooo/build_simulations.py --size 16 --fp-domain-trace \
  --name new_fp_base
python3 experiments/rsd_ooo/build_simulations.py --size 16 --fp-domain-trace \
  --fp-candidate experiments/rsd_ooo/formal/generated_scheduler_nofp \
  --name new_fp_cut

# Audit the retained datasets without rerunning RTL.
python3 experiments/rsd_ooo/summarize_scheduler_sweep.py
python3 experiments/rsd_ooo/summarize_fp_scheduler.py
python3 experiments/rsd_ooo/summarize_prf_sweep.py
```

The scheduler and FP summarizers also accept `--results-root` for fresh datasets
with the same variant/group layout. The PRF summarizer currently audits the
retained fixed directory layout. A fresh complete reproduction must run all
listed variants and the separate `Asm/FP` controls, not merely build them.

For the two no-FP builds above, these commands generate the full 14-pair dataset
and both FP controls. The cut's FP control is expected to return 1 because it
does not complete outside the contract; retain that return code. The final
summarizer explicitly checks that expected negative outcome.

```bash
for variant in base cut; do
  python3 experiments/rsd_ooo/run_workloads.py \
    --simulator "experiments/rsd_ooo/results/new_fp_${variant}/VMain_Zynq_Wrapper" \
    --output "experiments/rsd_ooo/results/new_fp/${variant}/diagnostics"
  python3 experiments/rsd_ooo/run_applications.py \
    --binary "experiments/rsd_ooo/results/new_fp_${variant}/VMain_Zynq_Wrapper" \
    --output "experiments/rsd_ooo/results/new_fp/${variant}/applications"
  fp_control_rc=0
  python3 experiments/rsd_ooo/run_upstream_tests.py --tests Asm/FP \
    --binary "experiments/rsd_ooo/results/new_fp_${variant}/VMain_Zynq_Wrapper" \
    --output "experiments/rsd_ooo/results/new_fp/${variant}/fp_control" || fp_control_rc=$?
  printf '%s\n' "$fp_control_rc" > "experiments/rsd_ooo/results/new_fp/${variant}/fp_control/runner.exitcode"
done
python3 experiments/rsd_ooo/summarize_fp_scheduler.py \
  --results-root experiments/rsd_ooo/results/new_fp
```

To regenerate the scheduler proof itself, run
`python3 experiments/rsd_ooo/formal/prove_scheduler_nofp.py` before the generator.
That driver requires the pinned Yosys/slang tools at
`tools/oss-cad-suite-20261104/oss-cad-suite/bin` and the Z3 solver; it writes the
base, induction, cover and no-contract counterexample artifacts. Reusing the
retained proof avoids rerunning those checks, while the generator still rejects
stale source or harness hashes.

For a fresh combined test, run from the project root after the bootstrap and
LSQ candidate-generation steps in the main README and the scheduler generator
above. These commands create both
original and combined outputs; they do not overwrite the retained experiment:

```bash
python3 experiments/rsd_ooo/build_simulations.py --size 16 --fp-domain-trace \
  --name new_combined_baseline
python3 experiments/rsd_ooo/build_simulations.py --size 16 --fp-domain-trace \
  --candidate experiments/rsd_ooo/formal/generated \
  --fp-candidate experiments/rsd_ooo/formal/generated_scheduler_nofp \
  --name new_combined_cut
python3 experiments/rsd_ooo/run_workloads.py \
  --simulator experiments/rsd_ooo/results/new_combined_baseline/VMain_Zynq_Wrapper \
  --output experiments/rsd_ooo/results/new_combined/base --filter stream
python3 experiments/rsd_ooo/run_workloads.py \
  --simulator experiments/rsd_ooo/results/new_combined_cut/VMain_Zynq_Wrapper \
  --output experiments/rsd_ooo/results/new_combined/diagnostics --filter stream
python3 experiments/rsd_ooo/summarize_combined.py \
  --baseline experiments/rsd_ooo/results/new_combined/base \
  --results-root experiments/rsd_ooo/results/new_combined
```
