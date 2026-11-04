# RSD out-of-order Pscorr experiment

This experiment studies RSD's speculative RV32 core across its scheduler,
load/store queues, ROB, issue queue and physical registers. The source-grounded
`MICROARCH_INVENTORY.txt` also considers wakeup, rename, replay, prediction,
recovery, execution ports, caches and MSHRs; it separates completed experiments
from possible future cuts. A reservation station in this core spans the shared
issue queue, payload banks, producer-matrix wakeup network and selection logic.

There are three distinct kinds of evidence: automatic Pscorr on original
component logic supplied with proved invariants; manually identified and
locally proved source cuts; and performance experiments changing capacities.
Source cuts are not reported as automatically discovered transformations.

Completed direct RTL maps use the same SKY130 HD TT library and flip-flop
storage. Scheduler/SelectLogic falls from 21,735.8464 to 15,636.2464 um²
(28.06%), and the LQ+SQ pair from 86,273.9936 to 40,518.8608 um² (53.03%).
The corresponding whole-core queue cut saves only 0.4400%:
9,996,011.967981 to 9,952,029.785581 um². Component percentages do not describe
the whole core. Combining the scheduler and queue cuts reduces whole-core area
to 9,610,673.647983 um² (3.8549%), with identical capacity and FP configuration;
`results/synthesis/combined_physical_audit.json` verifies the exact three source
differences. The scheduler-only control reaches 9,659,860.822383 um² (3.3629%)
without requiring the memory-region contract. These are cell-area estimates,
not SRAM-macro or post-layout
results. The summaries under `results/synthesis/` bind the raw map artifacts
and source identities. Formal-AIG mapping includes auxiliary initial-state
encoding and is kept separate from these physical RTL numbers.

The four inherited-order whole-core scorr comparisons each reached their
3,600-second limit without an accepted optimized result. The additional
ISA-plus-executed-region run, baseline constant-only control, and three
prebalanced controls also timed out. The prebalanced run importing the proved
queue invariants likewise reached its limit. All ten completed correspondence
attempts therefore have recorded timeouts, not accepted optimized results;
see `results/synthesis/whole_core_summary.json`.
Prepared scripts and partial logs are never counted as completed optimization.

## Sources and scope

- Core: [RSD](https://github.com/rsd-devel/rsd), pinned revision
  `7b65f6ba0bce58d4d859082660123b7100aae975`, under `rsd/`.
- The baseline retains ROB64, IQ16, LQ16, SQ16, MSHR2, the upstream cache sizes,
  two-wide front end and floating-point configuration.
- Verilator 4.228 is isolated under `tools/verilator-4.228`. System Verilator
  5.020 failed on generated C++ array declarations; those logs are preserved.
- New synthesis uses the existing Pscorr lowering generator and ABC scorr,
  with a pinned modern yosys-slang frontend. Original Synlig failed on an RSD
  type declaration. Tool/source identities are recorded in run manifests.
- Experiment scripts, workloads, traces and manifests are kept here; the
  pinned synthesis tool is under the workspace's `tools/`. The paper includes
  `src/rsd_case_study.tex`. Existing manuscript changes are retained and
  bibliography files are not edited.

## Experimental distinctions

1. Capacity tuning compares 16/16, 8/8 and 4/4 load/store queues. It retains
   correctness/backpressure logic but changes scheduling. It is not a
   cycle-equivalent Pscorr transformation. Independent sweeps cover ROB32/16,
   IQ32/64 and INT/FP physical registers 48/48 and 128/128. The 48-register
   variant requires an explicit reset-address guard and a matched guarded
   64-register control; see `SCHEDULER_RENAME.md`.
2. A manually identified dependence-check candidate retains 16/16 capacity
   and cuts historical address-match vectors in the original LQ and SQ.
   It retains same-cycle conflict checking, allocation, store commitment and
   recovery. `formal/generated/candidate_manifest.json` specifies the exact cut.
3. The candidate requires **every executed load**, including speculative,
   replayed and invalid-operand events, to have physical address `[21:16]==0`,
   and every executed store to have `[21:16]!=0`. RSD's physical addresses
   have 22 bits, including IO/cacheability tags. A property of committed
   instructions is insufficient. See `formal/REVIEW_NOTES.txt`.
4. Synthesis compares unconditional processing, an ISA opcode-class superset,
   the dependence cut, and their combination at matched capacities. A separate
   ISA-plus-region-assumptions variant tests automatic discovery without the
   manual cut. The ISA
   assumptions include valid wrong-path predecode instructions, SYSTEM and
   FENCE, and exclude FP and RV32M. They are not an exact RV32I decoder.
   See `synthesis/README.md` for initialization domains and mapping flows.
5. A separate scheduler contract excludes the FP execution class from every
   actual scheduler write, including wrong-path work. Thirty-five assertions
   on the original Scheduler/SelectLogic establish inactive FP requests,
   grants and selections. The candidate ties only the FP-request vector to
   false, preserving all other classes and IQ16 capacity. FP loads/stores
   remain supported; this is not a proof for removing the FP register file.
6. Automatic component Pscorr retains original comparison/request expressions.
   With identical reset-masked output boundaries, imported proved invariants
   reduce final AND counts beyond event-only contracts from 2,847 to 2,767 for
   the scheduler and from 17,957 to 13,795 for LQ+SQ. Their reset-reachable
   proof domain and the arbitrary-initial-state controls differ explicitly.
   These are formal AIG metrics, not physical hardware area.

## Validated measurements

The broader results and reproduction recipes are in `SCHEDULER_RENAME.md`:

- The scheduler cut matches counters, serial output and four raw traces for
  12 diagnostic inputs and two applications. Three additional FP-memory-only
  pairs pass with exact traces and independent Spike signatures. An excluded
  FP-arithmetic test is retained as an expected failing negative control.
- Four ROB/IQ variants add 88 executions: 87 architectural completions and
  one bounded noncompletion. ROB32 CoreMark does not finish within 20 million
  cycles and has a sustained frozen resource trace. This is an observed
  failure, not a universal deadlock proof. IQ32/64 increase benchmark-loop
  cycles for both applications.
- Three PRF variants add 69 executions including FP validation; all complete
  architectural checks. Named watchdog diagnostics remain separately visible.
  The guarded 64-register control matches the original's cycles and traces.
  Matched guarded64/48 direct RegisterFile maps retain all functional ports and
  reduce component area from 1,864,740.934398 to 1,419,098.528 um² (23.8984%).
  This is a capacity tradeoff, not same-capacity Pscorr pruning; see
  `results/synthesis/registerfile_physical_audit.json`.
- Both source cuts together preserve all counters and four raw traces for
  six streaming inputs satisfying both contracts, at unchanged capacities.

RSD can print progress-watchdog messages without stopping or failing final
architectural checks. Summaries distinguish completed architectural checks,
named diagnostics and bounded noncompletion. No named non-watchdog assertion
failure was found in these broader runs. One empty-message assertion cannot
be recovered reliably from the logs; this is not exhaustive assertion coverage.

`results/experiment_summary.json` and `experiment_comparison.csv` contain 48
RTL executions with paired comparisons: four algorithms, three input seeds, four variants.
All original/capacity variants match independent Python arithmetic signatures
and Spike. All 24 upstream tests across the monitored 16/8/4 capacities pass
their configured architectural-register and exact serial-output checks.

For stream-sum and stream-mix, all six baseline and cut executions satisfy the
strict region contract and have identical cycle counts, occupancy traces and
memory-event traces. Two occupied MSHRs remain observed. Representative seed-1
simulator-reported cycles (including software startup and serial output):

| Kernel | Original16 | Queue8 | Queue4 | Cut16 |
| --- | ---: | ---: | ---: | ---: |
| Stream sum | 12931 | 14168 | 31787 | 12931 |
| Stream mix | 16177 | 16177 | 27798 | 16177 |

Capacity effects are not monotonic across workloads. Seed-1 pointer chasing
takes 15,134 / 13,758 / 14,475 reported cycles at 16/8/4 entries, respectively,
with the same 4,198 committed instructions. The corresponding logged invalid
load-operand events fall from 3,326 to 2,454 to 480. This is an observed
scheduling tradeoff, not an equivalence or a proof that smaller queues improve
performance generally.

Pointer chasing deliberately tests a harder boundary: outputs happen to match
with the cut, but transient invalid-operand addresses violate the strict
contract 2583–2711 times in the baseline runs. Those runs are excluded from
positive contract claims. The alias-feedback negative control produces wrong
checksums with the cut for all three seeds; these failures must remain visible.

Original/cut matches on sampled traces do not prove full-core equivalence.
The actual unmodified LQ/SQ RTL has 36 assertions proved with reset base checks
and successful temporal induction, plus a reached nonvacuity cover:
`formal/results/actual_lsq/summary.json`. The broader consumer-mask relation is
source-audited rather than a full-core RTL equivalence proof. No proof here
establishes all-input adherence of an arbitrary application to the contract.

Observed occupancy peaks are not formal depth bounds. RSD admission uses
`count <= depth - rename_width - 1`; physical depth must include allocation
slack. Cache response latency is not complete allocation-to-release lifetime.
First-free MSHR allocation also needs pre-edge admission analysis: a slot may
be allocated in the same cycle another slot releases.

The additional controlled latency experiment is in `results/latency_summary.json`
and `.csv`: 36 runs form 18 baseline/cut pairs (six streaming inputs at read
pipeline depths 5, 10 and 20). All checks pass, with exact cycles and all five
raw traces identical in each pair. Read/write busy-count parameters 2 (observed
minimum accepted-request gap 3 cycles), jitter modulo 10 with seed 1987534242,
caches, LQ/SQ16 and MSHR2 remain fixed. For seed-1
stream-sum, measured read-response maxima are 22/27/37 cycles while complete
MSHR-valid intervals reach 37/39/50 cycles. Pipeline stages, request latency and
MSHR lifetime are distinct measurements. See `summarize_latency.py`; partial
intervals are recorded separately. Earlier `deep_base_p5` backing-memory CSVs
used an optimized-away alias and must not be used for response-latency claims;
the `latency_*` runs use corrected typed accessors on actual pipeline state.

## Reproduce and inspect

Run from the workspace root. To audit the retained data and rebuild the paper:

```bash
python3 experiments/rsd_ooo/summarize_experiment.py
python3 experiments/rsd_ooo/summarize_latency.py
python3 experiments/rsd_ooo/summarize_applications.py
python3 experiments/rsd_ooo/summarize_scheduler_sweep.py
python3 experiments/rsd_ooo/summarize_prf_sweep.py
python3 experiments/rsd_ooo/summarize_fp_scheduler.py
python3 experiments/rsd_ooo/summarize_fp_memory.py
python3 experiments/rsd_ooo/summarize_combined.py
python3 experiments/rsd_ooo/synthesis/collect_results.py
scripts/build_paper.sh
```

To regenerate the 48-run diagnostic comparison, use fresh result/build names.
The runners reject existing case directories to prevent stale output from
being counted as successful. The candidate run returns 1 because its three
aliasing negative controls must produce wrong checksums; the final summarizer
requires those exact failures, successful completion, and six positive cases.

```bash
set -e
bash experiments/rsd_ooo/bootstrap_rsd.sh
bash experiments/rsd_ooo/bootstrap_verilator.sh
python3 experiments/rsd_ooo/build_workloads.py
python3 experiments/rsd_ooo/formal/prove_nonalias.py
python3 experiments/rsd_ooo/formal/prove_actual_lsq.py
python3 experiments/rsd_ooo/formal/make_nonalias_candidates.py
pscorr_rsd_new_results=experiments/rsd_ooo/results/new_diagnostics
python3 experiments/rsd_ooo/run_workloads.py --spike \
  --simulator /home/allenjin/riscv/bin/spike \
  --output "$pscorr_rsd_new_results/spike_oracle"
for size in 16 8 4; do
  python3 experiments/rsd_ooo/build_simulations.py --size "$size" \
    --name "repro_lq${size}_sq${size}"
  python3 experiments/rsd_ooo/run_workloads.py \
    --simulator "experiments/rsd_ooo/results/repro_lq${size}_sq${size}/VMain_Zynq_Wrapper" \
    --output "$pscorr_rsd_new_results/kernels_monitored${size}"
  python3 experiments/rsd_ooo/analyze_traces.py \
    "$pscorr_rsd_new_results/kernels_monitored${size}"
done
python3 experiments/rsd_ooo/build_simulations.py --size 16 --name repro_cut16 \
  --candidate experiments/rsd_ooo/formal/generated
pscorr_rsd_cut_exit=0
python3 experiments/rsd_ooo/run_workloads.py \
  --simulator experiments/rsd_ooo/results/repro_cut16/VMain_Zynq_Wrapper \
  --output "$pscorr_rsd_new_results/kernels_regioncut16" || pscorr_rsd_cut_exit=$?
test "$pscorr_rsd_cut_exit" -eq 1
python3 experiments/rsd_ooo/analyze_traces.py \
  "$pscorr_rsd_new_results/kernels_regioncut16"
python3 experiments/rsd_ooo/summarize_experiment.py \
  --results-root "$pscorr_rsd_new_results"
```

The independent 36-run latency experiment requires deep traces; its recipe is
in `LATENCY.md`. Application sources, benchmark-loop cycle scope and the
six-run reproduction recipe are in `APPLICATIONS.md`. The scheduler,
ROB/IQ/PRF and combined-cut recipes are in `SCHEDULER_RENAME.md`.

The three FP-memory boundary cases use `FLW`/`FSW` through f0 and f31,
including raw NaN payloads, and check copied words using integer arithmetic.
To reproduce them using the FP-monitoring baseline/cut builds documented in
`SCHEDULER_RENAME.md`, choose fresh names:

```bash
python3 experiments/rsd_ooo/build_fp_memory_workload.py \
  --output experiments/rsd_ooo/fp_memory_workloads_repro
pscorr_rsd_fp_workloads=experiments/rsd_ooo/fp_memory_workloads_repro
pscorr_rsd_fp_results=experiments/rsd_ooo/results/fp_memory_repro
python3 experiments/rsd_ooo/run_workloads.py --spike --spike-isa rv32imf_zicsr \
  --simulator /home/allenjin/riscv/bin/spike \
  --workloads "$pscorr_rsd_fp_workloads" --output "$pscorr_rsd_fp_results/spike"
python3 experiments/rsd_ooo/run_workloads.py \
  --simulator experiments/rsd_ooo/results/new_fp_base/VMain_Zynq_Wrapper \
  --workloads "$pscorr_rsd_fp_workloads" --output "$pscorr_rsd_fp_results/baseline"
python3 experiments/rsd_ooo/run_workloads.py \
  --simulator experiments/rsd_ooo/results/new_fp_cut/VMain_Zynq_Wrapper \
  --workloads "$pscorr_rsd_fp_workloads" --output "$pscorr_rsd_fp_results/scheduler_cut"
python3 experiments/rsd_ooo/summarize_fp_memory.py \
  --workloads "$pscorr_rsd_fp_workloads" --results-root "$pscorr_rsd_fp_results"
```

`build_workloads.py --prefix` selects a different RISC-V toolchain. Workload
manifests record compiler commands and ELF/hex hashes. These short kernels are
diagnostics, not substitutes for a general application benchmark suite.
`run_workloads.py` requires a complete exact serial signature, explicit PC goal,
and no timeout or identifiable RSD/runtime diagnostic; the upstream simulator's
exit status alone does not establish success. RSD assertion macros only print
messages, so `rsd_log_checks.py` derives named diagnostic patterns from the pinned
source. One empty-message assertion cannot be identified retrospectively in
logs; these checks do not claim exhaustive internal-assertion coverage.
The region-cut alias runs intentionally make that
runner return nonzero; the paired summarizer checks these expected failures.

`resource.csv` contains post-rising-edge occupancy and settled next-edge event
signals. Startup initializes freelists, so whole-program IQ maxima must not be
interpreted as kernel demand. Deep-monitor builds also emit predecode, MSHR and
backing-memory traces. Synthesis logs under `results/synthesis/` retain both
failed frontend attempts and current runs; only completed validated result
records may support hardware claims.
