# Automatic storage ODC extension: static feasibility review

This is a source review plus a unit-validated generic prototype, not a LEN5 proof
or area result.
Sources are the official LEN5 pre-FPU revision
`14291dcc5bef181085d001c5a29e7f4fc4cbc8e9`, already qualified in
`len5/results/pre_fpu_frontend/manifest.json`. Paths below are relative to that
revision. No capacity parameter should change.

## Actual allocator and storage

`rtl/expipe/exec-units/arith_rs.sv:65-113` has eight 3-bit state words at the ALU
configuration, plus a 217-bit payload per entry: 4 control bits, three 5-bit ROB
tags, three 64-bit values, and 6 exception bits. This is a raw RTL width, not a
mapped saving; the ALU's constant exception wiring already permits baseline
cleanup. `len5_config_pkg.sv:80-82` fixes ALU_RS_DEPTH=8,
ALU_SPILL_SKIP=1, and ALU_RR_ARBITER=1. Both payload and state reset to zero/EMPTY.

The allocator is priority based, **highest empty index first**.
`arith_rs.sv:350-358` instantiates `prio_enc` without overriding INV;
`rtl/common/prio_enc.sv:19-63` defaults INV=0 and the last set input in the
ascending loop wins. If lifetime constraints make some entries unreachable,
the low-index entries are the candidates. Execution and CDB selectors use the
configured round-robin arbiters; replacing them with priority selectors would
change the baseline.

`empty` depends on the current state. A simultaneous removal cannot make its
slot available to insertion until the following cycle. Consequently, peak
post-edge occupancy K does not imply that only K priority slots are ever used.
The proof must cover admission-time occupancy and this reuse delay. A hand
trace with both operands ready, a combinational ALU, and uninterrupted CDB
service has two resident entries but uses three highest slots; this is only a
candidate bound to prove, not an assumption or a validated result.

## Context needed for a legitimate bound

ALU latency alone is insufficient. The state machine can wait indefinitely for
operand forwarding, execution acceptance/results, or CDB acceptance
(`arith_rs.sv:153-230`). The native `alu_unit.sv` connects the actual ALU and RS;
it should be included rather than replacing EU handshakes with assumed service.
`rtl/expipe/commit-unit/rob.sv:264` makes ROB CDB readiness constant one, but the
real `cdb.sv`/`cdb_arbiter.sv` and competing units still determine which result
is served. The highest-priority channel can defer others. Operand readiness is
computed from register-status and ROB/forwarding paths in
`issue-unit/issue_stage.sv:375-419`.

Prefer proving the candidate within the original whole-core context under
external instruction/timing assumptions. If decomposition is required, first
prove the exact component premises from that original context. Such premises
must cover operand readiness or bounded forwarding, result/tag legality,
service/grant availability, flush/reset handling, and interference. Do not
assume an occupancy bound, slot validity, allocator index range, or arbitrary
internal `ready=1` simply because these make storage removable. An ISA profile
using ready architectural sources can be considered, but readiness must follow
from the real issue path and the declared instruction restriction.

## Smallest reusable analyzer extension

Start with generic scalar combinational-output constant candidates. Enumerate
both 0 and 1 for unique-driven, one-bit `$eq` and `$logic_not` outputs, optionally
extending to other scalar logic. A source-cone regex may select the ALU RS;
neither safe slot indices nor the successful constant is supplied. Insertion
guards such as `new_idx==i`, state comparisons, and readiness comparisons then
enter the same automatic search.

For each candidate, replace that scalar cell with a one-bit `$pos` constant
driver on the same output wire. This preserves every port/net name and every
other original driver. Reject outputs aliasing a module input or FF Q bit,
multiple drivers, or a multi-output cell. A proved-false insertion guard
can enable ordinary constant propagation through the original EMPTY reset and
state transitions; unreachable execution/CDB selections may then make payload
registers dead. The amount of cleanup must be measured, not presumed.

Reuse `export_design`, `prove_pair`, immutable shared harnesses, source hashes,
initial-state handling, and the fail-closed PDR gate. Test every cumulative
trial against the original, and re-prove the final combined RTL after ordinary
cleanup. Unknown, timeout, and bounded-only success remain rejection. A quick
bounded counterexample can screen candidates but cannot certify them.

Only if this scalar-control search cannot expose storage should direct state-bit
substitution be added. It must remove the corresponding D/Q bit and parameters,
maintain aliases/init semantics, and avoid driving a constant from a live FF.
The optional continuing-state correspondence assertion may need disabling for
genuine state-ODCs; initial coupling and all functional observations remain.
Raw output payloads when valid is false require an explicit consumer audit, not
silent masking. Preserve the original reset protocol and define when outputs
become meaningful during reset before accepting any constant-state rewrite.

Decisive evidence would include native fixed-capacity source hashes, automatically
enumerated accepted/rejected candidates, positive unbounded proof, relaxed
timing counterexamples, nonvacuous dynamic-issue covers, actual dead-storage
cleanup, and matched full-core mapping. The previous sub-percent pilot remains
a regression; these source observations do not establish a material saving.

## Implemented generic entry point

`odc/state_candidates.py` implements `scalar_constant_candidates` and
`replace_scalar_constant`. `scripts/analyze_state_odc.py` runs identity,
cumulative-original, and final-combined proofs. It searches at most 32 probes
by default; `--max-probes` changes that explicit budget. `--scope` selects a
source cone without prescribing a successful bit value. Continuing internal
state assertions are off by default (`--no-state-helper`); `--state-helper`
opts in. Initial pairing and harness observations remain in both modes.

```sh
python3 scripts/analyze_state_odc.py flattened_hardware.json \
  --top Original --candidate-top Candidate --harness shared_miter.sv \
  --output /tmp/state-odc-run --scope 'reservation_station' \
  --max-probes 32 --engine pdr --abc /usr/local/bin/abc --no-state-helper
```

Actual unit tests prove a nonconstant predicate can be replaced when its only
effect is hidden state; reject both constants for a visible predicate; and
reject the second of two individually safe replacements when their combination
changes an output. The final design is re-proved in each successful search.
Structural tests check input/state/multiple-driver exclusions and preservation
of all other cells and named ports. No larger-core optimization has run yet.

The focused suite passed 83 tests, including 11 tests for this scalar extension
and reset-only initialization checks under both proof engines:

```sh
PYTHONPATH=../PdatDsl python3 -m pytest -q \
  tests/unit/test_state_candidates.py tests/unit/test_temporal_odc.py \
  tests/regression/test_sec_fail_closed.py tests/regression/test_odc_analysis.py
```
