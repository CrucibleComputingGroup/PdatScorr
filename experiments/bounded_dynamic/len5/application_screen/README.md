# Finite streaming and external timing screen

Both platforms run the unchanged pre-FPU LEN5 core with the same capacities,
two-entry fetch FIFO, and 64-element streaming program. `run_streaming.py`
checks all 64 output stores and the exit store. The external instruction
acceptance gate in `qualify_simulation.py --instruction-min-spacing 2` gates
both endpoints of the request handshake; it preserves native flush and
response behavior. This is a platform comparison, not software optimization
overhead or a resource reduction.

| Padded v2 workload | Native platform | Minimum fetch spacing 2 |
|---|---:|---:|
| Reported CPU cycles | 805 | 931 |
| Maximum live ALU entries | 6 | 2 |
| Allocated ALU indices | 1–7 | 5–7 |
| Complete load responses | 65 | 65 |
| Load response latency | 3 cycles | 3 cycles |
| Load exceptions | 0 | 0 |

Both traces retain actual out-of-order ALU execution. The gated platform takes
15.65% more reported cycles. Its returned fetches all take two cycles; native
backpressure produces fetch intervals of two, three, or seven cycles. Peak
occupancy two still uses three distinct slots. These finite traces establish
neither an occupancy invariant nor correctness of a hardware removal.

The v1 image left address `0x1200` uninitialized. Both v1 traces have a 65th
speculative load there, returning load-access-fault code 5 after a flush;
their correct architectural stores do not qualify an exception-free platform
assumption. Version 2 explicitly initializes 128 zero RAM bytes at
`[0x1200,0x1280)`, preserving every original byte, including all instructions.
All 65 physical loads are audited in v2 and return without exception.

[FETCH_SPACING.md](FETCH_SPACING.md) documents edge sampling, handshake and
flush semantics, witnesses, limitations, and reproduction commands.
`analyze_fetch_spacing.py` derives transactions from the native VCD interface
and cross-checks the gated monitor CSV; it does not rerun simulation.
`collect_fetch_spacing.py` copies compact evidence and verifies source hashes,
identical core files and capacities, image padding, completion, and faults.

The frozen compact packages are `evidence/fetch_spacing_v2` and
`evidence/fault_control_v1`. Each has a `SHA256SUMS` and original absolute source
paths. Regenerate into fresh directories with `collect_fetch_spacing.py
--output NEW_DIRECTORY`, adding `--workload-version 1` for the fault control.
Full waveforms remain under
`/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build/streaming*_v{1,2}`;
their hashes are retained in the timing summaries. The original text evidence
is under `../results/streaming*_v{1,2}`. These packages contain no formal proof
results and make no area claim.

## Certified decoder preprocessing

`--decoder-certificate` imports the exact-alphabet decoder substitution only
after rerunning the certificate's frozen verifier in the new query directory.
The fresh certificate must equal the supplied certificate. The original native
JSON must match its source hash, and the imported native candidate may change
only the certified combinational cells. Both native ALU observation ports are
added afterward. No storage driver, capacity, or extra formal premise is changed.

Import requires the immutable instruction ROM, zero payload on instruction
faults, and native initial reset. A strict parser checks every ROM word plus
zero against the certificate's exact alphabet. The certificate premise applies
only when `rst_ni && instr_rvalid_i`; invalid and reset-cycle instruction data
remain unrestricted. The verifier also binds the instruction-domain induction
and all thirteen decoder output comparisons. Withdrawn certificates, changed
sources/verifiers, extra ROM words, and unsupported fault/reset domains are
rejected. Inputs are captured and checked again after verifier replay.

The first query with this preprocessing and no datapath abstraction returned
`UNDECIDED` at the 120-second budget. It accepted no timing-induced hardware
optimization. Exact scripts, certificate replay, source/probe checks, logs,
and hashes are retained in
[`evidence/certified_decoder_admission_v1/PROVENANCE.json`](evidence/certified_decoder_admission_v1/PROVENANCE.json).
This result does not establish an admission bound or storage saving. The
program-only decoder substitution has its own separate certificate.

Reproduce with fresh output directories after preparing the pinned frontend
and the certificate's source-bound proof directories:

```sh
python experiments/bounded_dynamic/len5/application_screen/formal_screen.py \
  --disassembly experiments/bounded_dynamic/len5/results/streaming_fetchgap2_v2/program.disasm \
  --program-hex experiments/bounded_dynamic/len5/application_screen/evidence/certified_decoder_admission_v1/run/program.hex \
  --zero-fault-data \
  --decoder-certificate experiments/bounded_dynamic/len5/isa_baseline/results/program_alphabet_certificate_v3.json \
  --output /tmp/len5-certified-decoder-query --gap 2 --threshold 4 \
  --datapath-abstraction none --engine pdr --timeout 120
```

The certificate deliberately records exact proof/source paths and hashes. If
those dependencies are regenerated elsewhere, create a new certificate rather
than editing its bindings. `collect_certified_screen.py --build RUN --output
FRESH_DIRECTORY` collects an existing run without launching a solver.

## Source-bound instruction-domain lemmas

`--word-domain-lemmas --rom-domain-proof CERTIFICATE` additionally imports seven
already-proved word-domain conclusions: six native instruction storage words
and the original decoder input. `domain_lemmas.py` reconstructs the native FF
slices, all 36 retained combinational controls, and the entire theorem harness.
It replays the frozen certifier and regenerates the small projection's JSON and
SMT exactly. The original base and temporal-induction proofs establish these
conclusions under initial native reset and the reset-qualified response-domain
premise. No admission, occupancy, readiness, or tag assumption is introduced.

`rom_domain_import.py` discharges that external premise using the exact
generated Harvard producer theorem in `evidence/rom_domain_v2`. The proof cuts
every core output to an arbitrary input, preserves the ROM and memory pipeline
source, and retains only the original initial-reset assumption. Its three
reset-qualified domain assertions pass base and induction. The importer checks
the exact current harness, native port descriptor, ROM image, source/model/log
hashes, and a fresh model-export replay. Both theorem dependency sets are checked
again after each solver run.

Native `core.json` and `core.v` remain free of formal properties. A separate
`lemma_core.json` adds 119 predicate cells containing exactly seven derived
assumptions. The composed query retains the original three safety assertions
and eight assumptions: initial reset plus those seven proved conclusions.
The query model is never an implementation or input to physical mapping.

With native arithmetic, the inspected model contains 617,079 AIG AND nodes and
24,421 latches. PDR reached its 120-second limit without proving or refuting the
query. A separate 64-frame BMC request on the same AIG reported no assertion
failure in 26 frames before exhausting the 120-second limit; it did not complete
the requested horizon. Neither result accepts storage removal. Source, theorem
replays, solver logs, and hashes are in
[`evidence/word_lemmas_admission_v1/PROVENANCE.json`](evidence/word_lemmas_admission_v1/PROVENANCE.json).

The optional `alu_mul` proof abstraction is applied only after certification and
lemma import. It replaces two whole 64-bit combinational payload drivers with
arbitrary values while preserving all native state, branch logic, the certified
instruction projection, and all 119 lemma cells. This includes every original
trace, so an unbounded safety proof transfers to the native design; an abstract
counterexample needs native concretization. Native hardware is still exported
separately. The corresponding query is `abstract_query_core.json`, never a
physical candidate. The separate `alu_mul_branch_taken` mode adds one arbitrary
branch-result bit, with the same state, driver, and projection-preservation
checks. It can introduce spurious branch outcomes and counterexamples; it is
never a native hardware rewrite.

| Prepared proof model | AIG ANDs | AIG latches | Solver outcome |
|---|---:|---:|---|
| Native arithmetic plus seven word lemmas | 617,079 | 24,421 | PDR unknown; BMC reported 26 frames before its limit |
| ALU/multiplier payload abstraction | 530,756 | 22,725 | PDR unknown; BMC timed out before completing its 64-frame request |
| ALU/multiplier plus branch-result abstraction | 525,567 | 22,469 | Preparation only; no backend run |

All three native hardware exports have the same SHA256. State disappears only
from unused cones of the lowered proof models. The ALU/multiplier PDR run
returned `UNDECIDED` at its 120-second budget. Its BMC run printed frame 25 before
the outer 125-second timeout; there is no completed-horizon result or
counterexample. These are bounded resource budgets, not isolated performance
measurements. The compact records are
[`word_lemmas_alu_mul_admission_v1`](evidence/word_lemmas_alu_mul_admission_v1/PROVENANCE.json)
and the unsolved
[`word_lemmas_branch_preparation_v1`](evidence/word_lemmas_branch_preparation_v1/PROVENANCE.json).

To reproduce with fresh directories and the certificate's exact dependencies:

```sh
python experiments/bounded_dynamic/len5/application_screen/formal_screen.py \
  --disassembly experiments/bounded_dynamic/len5/results/streaming_fetchgap2_v2/program.disasm \
  --program-hex experiments/bounded_dynamic/len5/application_screen/evidence/certified_decoder_admission_v1/run/program.hex \
  --zero-fault-data \
  --decoder-certificate experiments/bounded_dynamic/len5/isa_baseline/results/program_alphabet_certificate_v3.json \
  --word-domain-lemmas \
  --rom-domain-proof experiments/bounded_dynamic/len5/application_screen/evidence/rom_domain_v2/summary.json \
  --output /tmp/len5-word-lemma-prepare --gap 2 --threshold 4 \
  --datapath-abstraction none --engine prepare --timeout 120
python experiments/bounded_dynamic/len5/application_screen/solve_prepared.py \
  --prepared /tmp/len5-word-lemma-prepare --output /tmp/len5-word-lemma-pdr \
  --engine pdr --timeout 120
python experiments/bounded_dynamic/len5/application_screen/solve_prepared.py \
  --prepared /tmp/len5-word-lemma-prepare --output /tmp/len5-word-lemma-bmc \
  --engine bmc --frames 64 --timeout 120
```

Use `--datapath-abstraction alu_mul` and another preparation directory to build
the reviewed overapproximation. `solve_prepared.py` checks the inspected AIG,
native/query sources, and all theorem dependencies before and after solving.
`collect_lemma_screen.py --prepared RUN --solver PDR_RUN --solver BMC_RUN
--output FRESH_DIRECTORY` packages existing results without running a solver.
