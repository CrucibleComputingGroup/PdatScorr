# RSD synthesis artifacts

The source is RSD revision `7b65f6ba0bce58d4d859082660123b7100aae975`.
`prepare_core.py` makes an isolated copy; it does not modify the checkout.
The matched final runs retain 16-entry load and store queues, two MSHRs,
two integer issue lanes, and the floating-point pipeline. All debug and
performance observation ports are disabled consistently. The top is the
complete `Core`, including its caches and register memories, with those memories
mapped to flip-flops. These are synthesis cell-area estimates, not a placed
SoC or an SRAM-macro implementation.

## Frontend and compatibility

The old bundled Synlig frontend cannot elaborate the RSD global packed types.
The final frontend is Yosys/slang from OSS CAD Suite 20261104; its release
archive provenance is in `tools/oss-cad-suite-20261104/provenance.json`.
Use `read_slang --single-unit --no-implicit-memories` through the generated
script. The completed whole-core physical maps retain that modern Yosys
process through mapping. System Yosys 0.33 is used for component physical
maps and optional formal-AIG mapping, matching the inherited `abc -fast` flow.
Executable/plugin and Liberty hashes are recorded in
`results/synthesis/tool_versions.json`; the standalone scorr ABC and the ABC
used internally by system Yosys mapping are separately identified.

RSD's fetch flush loop initializes entries inside a loop containing `break`.
Slang introduces a false combinational cycle for that source form. The common
`compat/fetch_flush_patch.json` moves initialization before the loop.
The extracted original and canonical functions agree on every one of their
32 input combinations at the actual fetch width of two; see
`results/synthesis/compat/summary.json` and `exhaustive.log`. This is a local
source equivalence check, not a whole-core sequential-equivalence certificate.
No other combinational-cycle cuts are used in the final runs.

## Matched variants

The final result directories are `base_core_final`, `isa_core_final`,
`nonalias_core_final`, and `isa_nonalias_core_final` under `results/synthesis`.
Each contains its exact source snapshot, source hashes, elaboration and lowering
scripts, logs, and AIG export.

The ISA contract is a conservative RV32I opcode-class superset, including
fence and CSR classes, with RV32M OP encodings excluded. It applies to every
valid PreDecode pipeline lane when reset is low, including speculative work.
It is not a complete ISA legality predicate or a static proof of a binary.
The two ISA variants have two AIGER constraints, one per lane.

`isa_region_assume_core_final_v2` is the additional direct Pscorr test of
microarchitecture assumptions beyond the ISA contract. It retains the original
LQ/SQ RTL and adds only postreset assumptions on the execution flags and physical
addresses in `loadStoreUnitIF`, with one assumption per load/store lane. Its
control is `isa_core_final` and its initial-state treatment is identical.
This variant is distinct from the separately proved source comparator cuts.

`isa_region_lemmas_core_final` adds the 32 finished-entry region invariants
proved on the original actual LQ/SQ RTL. Each is guarded by `!port.rst` and
does not depend on register validity. The queue comparators are retained.
`proof_import.json` binds the imported expressions to original source hashes,
the checked harness, SMT model, and successful base/induction/cover logs.
This is the proof-guided microarchitecture experiment: local induction supplies
state facts to full-core correspondence. Its justification is explicitly
reset-conditioned and differs from the conservative arbitrary-initial-state
domain of the ISA and executed-region-only controls. It uses the same
prebalanced, full-correspondence, logic-only settings described below.

The region candidate replaces only historical load/store queue address matches
with false. The actual LQ/SQ induction and exact contract are documented under
`formal/results/actual_lsq` and `formal/generated/candidate_manifest.json`.
The source-level cut requires all executed load addresses to have physical
bits `[21:16] == 0` and all executed store addresses to have those bits nonzero,
including invalid-register and wrong-path execution. The same-cycle load
conflict logic is retained. This is a separately proved microarchitecture
transformation; do not describe it as a cut discovered automatically by scorr.

## Two area flows, kept separate

`core_direct_original` and `core_direct_region_cut` are the stopped legacy
physical RTL mapping attempts. They read normalized Verilog exported before `write_aiger -zinit`.
All assumptions are removed before mapping. The original uses the ISA snapshot
with its formal-only assumptions removed, so its functional RTL is the baseline.
The library is SKY130 HD `tt_025C_1v80`. The same Yosys/ABC commands and common
frontend adaptation are used in both runs.

`core_modern_direct_original` and `core_modern_direct_region_cut` are a separate
matched physical flow family launched after the legacy Verilog reread/mapping
spent over an hour in serialization and repeated optimization. The exact
prepared frontend and normalization run in one modern Yosys process, with no
Verilog reread or AIGER-zinit conversion. Mapping uses `/usr/bin/yosys-abc` and
the explicit legacy fast script `strash; dretime; map`, with the same Liberty.
Statistics precede optional Verilog export; no expensive export is requested
for these runs. ABC mapping temporary artifacts are retained. Do not mix an
area numerator/denominator across the two physical flow families.
`core_modern_direct_combined` additionally applies the proved Scheduler
FP-request cut, while `core_modern_direct_scheduler` applies that cut alone.
All four keep the same capacities and use the same modern physical flow.
The earlier legacy physical maps were explicitly stopped as redundant after
the modern pair completed; their status is `stopped_redundant_flow`, with the
completed replacement named in each manifest.

`run_backend.py` runs the actual existing Pscorr inductive-correspondence
algorithm on the whole-core AIG model. It uses `scorr -F 2 -C 30000 -S 20 -v`,
adding `-c -m` for constrained variants. A matched unconditional-scorr control
and a combinational-only no-scorr control distinguish ordinary cleanup from
constraint-driven correspondence. No `cycle 100` initial-state randomization
is applied. Assumptions are purged with `constr -r -p` only after scorr, and
the original output count is checked. The inherited `setundef -zero` is used
consistently. `write_aiger -zinit` encodes unknown initial flip-flop states with
additional primary inputs and muxes. The area from mapping this formal model
must be labeled separately from the physical RTL area above.

The whole-core scorr runs do not add a startup-reset protocol assumption.
Their ISA optimization therefore has a conservative arbitrary-initial-state
domain; stale initially valid pipeline work can limit pruning. The separately
proved region rewrite instead has a reset-conditioned contract. Comparing the
sizes of region-cut and original AIG models does not establish equivalence
between their arbitrary initial states. No initial-state randomization or
bounded no-counterexample result repairs that difference in proof scope.

The separate baseline `mapped_scorr_constants` run uses `scorr -k` with the
same depth, conflict limit, and simulation setting to restrict candidates to
constants. Initially attempted constrained `-k` controls were stopped after
a GDB-owned probe of the installed binary showed `fConstCorr=1` still enters
`Ssw_ClassesPrepareSimple` under constraints. Thus `-k` does not narrow their
candidate initialization. Those runs are labeled `stopped_redundant_control`
and are not presented as a distinct optimization method. The diagnostic
transcript is `results/synthesis/scorr_runtime_probe/probe_gdb.log`.

`logic_scorr_prebalanced` is a second explicit scalability control: baseline,
ISA, and ISA+region receive `balance -l` before full correspondence, followed by
the same scorr settings. This changes Boolean representation only. The retained
depth probe found that balancing reduced the baseline strashed depth from 3006
to 195 with unchanged I/O/latch counts. The scripts retain `prebalanced.aig`
and both sets of statistics. With `--logic-only`, successful runs end with
`complete_logic`, checked output/constraint counts, and AIG sizes/runtime;
they do not claim mapped area. This is distinct from the original inherited
ordering and from the constant-only runs.
`base_core_final/logic_no_scorr_prebalanced` supplies the matched prebalanced
combinational-only control.

The backend refuses existing output directories and records failures and time
limits explicitly. A completed process and a parsed final mapped area are
required before its status becomes `complete`; a bounded run without a
counterexample is never treated as a proof. `collect_results.py` writes
`whole_core_summary.json` and refuses to count partial mapping logs as results.
Older failed frontend/backend attempts remain for diagnosis and are not the
matched final experiment.

For the separate LQ/SQ component, `lsq_direct_summary.json` describes direct RTL
mapping at the observation boundary in `formal/LSQObserved.sv`. Its percentage
is a component result and must not be reported as the whole-core reduction.

`lsq_lemma_reset_summary.json` describes a separate automatic Pscorr experiment
on original queue comparators. The baseline, execution-region-only, and
lemma-assisted variants have identical wrappers that force all 144 output bits
to zero during reset while preserving every internal reset transition. Their
source/import audit is `reset_observation_audit.json`. Lemma assistance reduces
ANDs and state beyond executed-region assumptions at this boundary; its area
is the mapped AIGER-zinit formal model and is separate from the direct physical
RTL result. The original unmasked boundary is a retained negative control:
there, execution-only and lemma-assisted optimization produce identical
17,849-AND/1,707-latch models and identical mapped formal-model area.

Outside memory, `scheduler_direct_summary.json` reports the actual Scheduler
and SelectLogic direct physical mapping for an externally proved no-FP-request
cut. All functional outputs/raw pointers and IQ16 capacity remain observed;
this does not remove payload RAM, the register file, or the full FP unit.
`scheduler_lemma_reset_summary.json` separately reports automatic Pscorr on
original Scheduler logic, comparing a reset-masked baseline, actual-write
no-FP admission assumptions, and those assumptions plus 16 proved live-entry
invariants. Its mapped area includes the formal AIG initialization encoding.
Source/proof imports and masks are independently audited in
`scheduler_direct_audit.json` and `scheduler_import_audit.json`.

`registerfile_direct_summary.json` is a distinct capacity/performance control:
64 versus 48 physical registers in each INT/FP bank, with an identical explicit
reset compatibility guard in both source snapshots. All functional ports,
raw tags, and 429 output bits are retained, with no assumptions or masks and
no AIGER-zinit conversion. This is not Pscorr pruning or equivalence for
unrestricted physical-register addresses. Source/boundary and mapping audits
are linked from the summary.

Runtime environment details are in `results/synthesis/runtime_environment.json`
(EPYC 9575F VM with 256 CPUs visible in the affinity mask). Optimization limits
are wall-clock budgets, with concurrent experiments on the shared VM; they
are not isolated performance measurements. The GDB diagnostics used separate
short-lived child processes and one interrupted stack sample per path. They
identify observed resimulation code paths, not a measured fraction of total
runtime or a general claim about Pscorr scalability on other models/settings.

## Final measured results and statuses

All four modern whole-core physical maps completed and were independently
audited. The source cuts were supplied from the local RTL proofs; scorr did
not discover these cuts automatically. Every result below uses the same
capacity, frontend, mapper, and Liberty. Areas include flop-mapped memories.

| Whole-core physical variant | Cell area (µm²) | Flip-flops | Reduction from original |
|---|---:|---:|---:|
| Original | 9,996,011.967981 | 167,332 | — |
| LSQ region cut | 9,952,029.785581 | 166,513 | 0.4400% |
| Scheduler FP-request cut | 9,659,860.822383 | 165,179 | 3.3629% |
| Both cuts | 9,610,673.647983 | 164,360 | 3.8549% |

The region cut requires the strict executed-address contract; the Scheduler
cut requires the actual-write no-FP contract. The combined result requires
both. The Scheduler-only result has no memory-region restriction. These are
reset-conditioned results, without a full-core sequential-equivalence proof.
`whole_core_modern_physical_summary.json` contains the sequential/combinational
area breakdown and links to raw statistics and manifests.

Component direct physical maps also completed: LSQ 86,273.9936 → 40,518.8608
µm² (53.03%); Scheduler/SelectLogic 21,735.8464 → 15,636.2464 µm² (28.06%).
The separate guarded PRF capacity control changes both banks from 64 to 48
entries: 1,864,740.934398 → 1,419,098.528 µm² (23.90%). Its measured performance
tradeoff and explicit reset compatibility change are separate from the
same-capacity pruning results.

For the automatic component experiments, reset-masked observation and imported
inductive lemmas expose savings beyond environment assumptions alone. These
are AIGER formal-model metrics, including initialization encoding:

| Original-RTL automatic component | Baseline ANDs / latches | Environment-only ANDs / latches | Environment + lemmas ANDs / latches | Additional mapped formal-model area reduction |
|---|---:|---:|---:|---:|
| LSQ | 18,145 / 1,707 | 17,957 / 1,707 | 13,795 / 1,595 | 16.96% |
| Scheduler/SelectLogic | 2,847 / 129 | 2,847 / 129 | 2,767 / 129 | 5.20% |

The unmasked LSQ boundary gave no added lemma benefit and remains a negative
control. The reset masks are an explicit observation contract, not a claim
of all-cycle equality at the original component boundary.

All ten planned whole-core monolithic correspondence attempts reached their
3,600-second wall limits without an accepted optimized model:

| Control family | Variants | Final outcome |
|---|---|---|
| Inherited full correspondence | Original, ISA, region source cut, ISA + region source cut, ISA + executed-region assumptions | 5 timeouts |
| Constant-only, unconstrained | Original | 1 timeout |
| Prebalanced full correspondence | Original, ISA, ISA + executed-region assumptions | 3 timeouts |
| Prebalanced proof-assisted full correspondence | ISA + executed-region assumptions + 32 proved lemmas | 1 timeout |

Two constrained constant-only attempts were stopped as redundant after the
installed-binary diagnostic; they are outside the ten timeout trials. The
inherited no-scorr control completed Boolean processing at 2,486,012 ANDs and
167,333 latches, but its optional mapping timed out during netlist export;
no mapped area is accepted. The prebalanced no-scorr control completed at
2,482,505 ANDs and 167,333 latches. Both preserve 141 ordinary outputs.
The two legacy physical maps are `stopped_redundant_flow`; all four modern
physical maps and both guarded PRF maps are `complete`. No planned jobs remain.

`collect_results.py` regenerates `whole_core_summary.json`,
`whole_core_modern_physical_summary.json`, `registerfile_direct_summary.json`,
and `whole_core_scorr_status.json`. The latter lists every planned trial,
elapsed optimization time, accepted-model status, and retained control result.
Timeouts describe these settings and wall budgets; they are not zero-gain
measurements or a general impossibility result.

## Reproduce in fresh output directories

Run from the repository root, with the pinned RSD checkout, tool suite, system
Yosys/ABC, and Liberty above already installed. The commands below reuse the
supplied proof and generated-candidate artifacts, validate them, and write
all new synthesis output below a unique directory. They do not overwrite the
recorded experiment. Paths must not contain whitespace because the inherited
Yosys command generator emits unquoted filenames.

The source-cut prerequisites are the actual-RTL proofs in
`formal/results/actual_lsq` and `formal/results/scheduler_nofp`, their matching
harness/source hashes, and the candidates in `formal/generated` and
`formal/generated_scheduler_nofp`. `prove_actual_lsq.py` and
`prove_scheduler_nofp.py` regenerate the proofs; run them in a separate copy
if fresh proof runs are desired, because they use fixed proof-result paths.
The candidate manifests bind the retained source edits to those proofs. The
following check verifies that the synthesis patches exactly reproduce the
certified candidate bytes; it does not replace the proofs.

```bash
set -euo pipefail
RSD_SYNTH="$PWD/experiments/rsd_ooo/synthesis"
RSD_FORMAL="$PWD/experiments/rsd_ooo/formal"
RSD_YOSYS="$PWD/tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys"
RSD_LIB="/opt/pdk/skywater-pdk/libraries/sky130_fd_sc_hd/latest/timing/sky130_fd_sc_hd__tt_025C_1v80.lib"
RSD_RUN="$(mktemp -d "$PWD/experiments/rsd_ooo/results/reproduce.XXXXXX")"
export RSD_SYNTH RSD_FORMAL RSD_RUN

python3 - <<'PY'
import hashlib, json, os
from pathlib import Path
s = Path(os.environ['RSD_SYNTH'])
f = Path(os.environ['RSD_FORMAL'])
src = f.parent / 'rsd/Processor/Src'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
lsq = json.loads((f/'results/actual_lsq/summary.json').read_text())
sch = json.loads((f/'results/scheduler_nofp/summary.json').read_text())
assert lsq['status'] == sch['status'] == 'passed'
assert lsq['property_counts']['assert'] == 36
assert sch['properties']['assertions'] == 35
assert sha(f/'LSQRegionProof.sv') == lsq['harness_sha256']
assert sha(f/'SchedulerNoFPProof.sv') == sch['harness_sha256']
for proof in [lsq, sch]:
    for rel, expected in proof['source_sha256'].items():
        assert sha(src/rel) == expected, rel
for old_path, expected in lsq['all_elaboration_source_sha256'].items():
    rel = old_path.split('/Processor/Src/', 1)[1]
    assert sha(src/rel) == expected, rel
for directory, logs in [('actual_lsq', ['base', 'induction', 'cover_nonvacuity']),
                        ('scheduler_nofp', ['contract_base', 'contract_induction', 'contract_cover'])]:
    for log in logs:
        assert 'Status: PASSED' in (f/'results'/directory/(log+'.log')).read_text()
lm = json.loads((f/'generated/candidate_manifest.json').read_text())
sm = json.loads((f/'generated_scheduler_nofp/candidate_manifest.json').read_text())
candidates = {}
for item in lm['files']:
    rel = 'LoadStoreUnit/' + Path(item['candidate']).name
    candidate = f/'generated'/Path(item['candidate']).name
    assert sha(src/rel) == item['source_sha256']
    assert sha(candidate) == item['candidate_sha256']
    candidates[rel] = candidate.read_text()
assert sha(src/'Scheduler/Scheduler.sv') == sm['source_sha256']
assert sha(f/'generated_scheduler_nofp/Scheduler.sv') == sm['candidate_sha256']
assert sha(f/'results/scheduler_nofp/summary.json') == sm['proof_summary_sha256']
candidates['Scheduler/Scheduler.sv'] = (f/'generated_scheduler_nofp/Scheduler.sv').read_text()
fetch = json.loads((s/'compat/fetch_flush_patch.json').read_text())
for name, wanted in [('nonalias_canonical_patches.json', set(candidates)-{'Scheduler/Scheduler.sv'}),
                     ('nofp_canonical_patches.json', {'Scheduler/Scheduler.sv'}),
                     ('combined_canonical_patches.json', set(candidates))]:
    patches = json.loads((s/name).read_text())
    assert patches[:1] == fetch
    assert {p['file'] for p in patches[1:]} == wanted
    for p in patches[1:]:
        assert p['old'] == (src/p['file']).read_text()
        assert p['new'] == candidates[p['file']]
print('Proof/source/candidate prerequisites match')
PY
```

Prepare and map the four matched physical variants. These commands perform
no AIG initialization conversion and preserve the existing capacities:

```bash
prepare_core() {
  python3 "$RSD_SYNTH/prepare_core.py" "$RSD_RUN/$1" \
    --frontend slang --no-implicit-memories --lq 16 --sq 16 --mshr 2 \
    "${@:2}"
}
prepare_core base_core_final --patches "$RSD_SYNTH/compat/fetch_flush_patch.json"
prepare_core nonalias_core_final --patches "$RSD_SYNTH/nonalias_canonical_patches.json"
prepare_core nofp_core_final --patches "$RSD_SYNTH/nofp_canonical_patches.json"
prepare_core combined_core_final --patches "$RSD_SYNTH/combined_canonical_patches.json"

for pair in base_core_final:original nonalias_core_final:region_cut \
            nofp_core_final:scheduler combined_core_final:combined; do
  python3 "$RSD_SYNTH/run_inprocess_core.py" \
    "$RSD_RUN/${pair%%:*}" "$RSD_RUN/core_modern_direct_${pair##*:}" \
    --yosys "$RSD_YOSYS" --abc /usr/bin/yosys-abc \
    --liberty "$RSD_LIB" --timeout 7200
done
```

For the monolithic Pscorr trials, prepare the ISA, execution-region, and
lemma models, then export the formal AIGs. The lemma option checks original
queue source hashes, proof harness hashes, and successful actual-RTL proof
logs before importing the 32 predicates. It requires the strict executed
regions and the proved 16-entry configuration. The two source-cut AIGs remain
separate controls with the external reset-conditioned justification above.

```bash
prepare_core isa_core_final --patches "$RSD_SYNTH/compat/fetch_flush_patch.json" --isa-rv32i
prepare_core isa_nonalias_core_final --patches "$RSD_SYNTH/nonalias_canonical_patches.json" --isa-rv32i
prepare_core isa_region_assume_core_final_v2 --patches "$RSD_SYNTH/compat/fetch_flush_patch.json" \
  --isa-rv32i --execution-regions
prepare_core isa_region_lemmas_core_final --patches "$RSD_SYNTH/compat/fetch_flush_patch.json" \
  --isa-rv32i --execution-regions --proven-region-invariants

for name in base_core_final isa_core_final nonalias_core_final isa_nonalias_core_final \
            isa_region_assume_core_final_v2 isa_region_lemmas_core_final; do
  "$RSD_YOSYS" -m slang -Q -T -s "$RSD_RUN/$name/synth.ys" \
    > "$RSD_RUN/$name/synth.log" 2>&1
done
```

The backend writes a failed result with a timeout stage and exits nonzero
when its budget expires. The helper below records that expected outcome and
continues the prescribed controls. Each optimization stage has its own
3,600-second limit; optional mapping has another limit of the same length.
Running this full set can take many hours. The `--logic-only` controls omit
mapping rather than accepting partial area reports.

```bash
backend() {
  local model="$1" mode="$2"
  shift 2
  if ! python3 "$RSD_SYNTH/run_backend.py" "$RSD_RUN/$model/core_yosys.aig" \
    "$RSD_RUN/$model/$mode" --abc /usr/local/bin/abc --yosys /usr/bin/yosys \
    --liberty "$RSD_LIB" --depth 2 --timeout 3600 "$@"; then
    printf 'Inspect recorded outcome: %s\n' "$RSD_RUN/$model/$mode/result.json"
  fi
}

for model in base_core_final isa_core_final nonalias_core_final isa_nonalias_core_final \
             isa_region_assume_core_final_v2; do
  backend "$model" mapped_scorr
done
backend base_core_final mapped_scorr_constants --constant-only
for model in base_core_final isa_core_final isa_region_assume_core_final_v2 \
             isa_region_lemmas_core_final; do
  backend "$model" logic_scorr_prebalanced --prebalance --logic-only
done
backend base_core_final mapped_no_scorr --no-scorr
backend base_core_final logic_no_scorr_prebalanced --no-scorr --prebalance --logic-only
python3 "$RSD_SYNTH/collect_results.py" --results "$RSD_RUN"
```

The collector will label component runs absent from this whole-core recipe
`not_started`; it never substitutes the archived component measurements.
