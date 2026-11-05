# Automatic phase-sharing control

No LEN5 bank merge was accepted. The final 64-bit candidate returned
`UNDECIDED` at its 120-second PDR budget. This experiment tests program-independent
lifetime ODCs as a control for the timing-constrained study; it does not establish
timing-induced savings or a mapped-area reduction. Compact records are in
[`results/phase_control_v1/summary.json`](results/phase_control_v1/summary.json).

The archived attempts predate the corrected symbolic-undefined frontend.
Historical successful subproofs require revalidation or a separate certificate
that their undefined choices are irrelevant; the target outcomes already
accepted no rewrite. Current `proof.py` uses the shared safe preparation helper
and archives its exact source for future runs. No historical solver artifact
has been overwritten. See
[`formal_frontend/README.md`](../../formal_frontend/README.md).

The source is unmodified PRE-FPU LEN5 commit
`14291dcc5bef181085d001c5a29e7f4fc4cbc8e9`. The original ALU reservation station
has eight entries. Every operand remains arbitrary and instructions may wait
for forwarding; flushes and competing CDB producers remain unrestricted. The
only temporal premise is the common native reset asserted at initial time.
Reset can assert again later. There is no instruction-class, queue-occupancy,
all-operands-ready, or service-latency assumption.

## Candidate generation and proof

`odc/bank_sharing.py` enumerates enabled-register pairs with identical width,
clock, and reset semantics. Version 1 supports `$dffe` and `$adffe` and rejects
incompatible or contradictory explicit initialization. A regex scopes the ALU
payload cone and a minimum width scopes the storage search; neither chooses
specific source rows or safe field pairs.

For each pair, a combinational SAT prefilter cuts every original register Q to
an arbitrary prestate input and checks that the two write enables cannot both
assert. This is a necessary prefilter, not an equivalence certificate: exclusive
writes may still overwrite live values. The first baseline has 24 64-bit banks,
276 compatible pairs, and 16 exclusive-write survivors. Their interpretation
as two operand/result alternatives per row is a result of enumeration, not an
input pairing rule.

The candidate deletes one bank, unions the active write enables, multiplexes
the two original write-data buses, preserves the native clock/reset, and
rewires both original Q uses to the shared bank. An explicit wrong-data
mutation is reserved for negative controls. A proposed rewrite is accepted
only through full two-copy output equivalence. Neither an ongoing state
correspondence nor a representation invariant is assumed. Initial states are
independent; the actual reset establishes the proof's reachable domain.

## Observation boundary

`AluObserved.sv` contains original ALU8, the original six-producer CDB, and
original ROB32, exporting all functional ROB outputs. Its 7,457-FF identity
PDR attempt reached its 120-second budget and returned `UNDECIDED`; it is
retained as a scalability diagnostic, not a failed correctness proof.

`AluCdbObserved.sv` uses the compositional boundary: original ALU8 and original
CDB, with an arbitrary downstream `rob_ready_i`. It exports every ready/valid
output and the global CDB payload qualified by global `cdb_valid_o`. The raw
global CDB variant is an alternative observation boundary. Qualifying a *local
ALU* payload by local valid is insufficient: the CDB arbiter retains producer
requests, so the real arbiter must remain inside the proof.

The qualified global CDB projection requires a separate proof that every real
downstream consumer ignores global payload when global valid is zero. The
consumer-closure experiment operates on the original whole-core netlist, pairs
arbitrary original prestate, and compares every next-state bit and actual core
output under two independent invalid CDB payloads. Its exact enable/reset
semantics and source hashes passed: all 297 actual core outputs and 24,151 exact
next-state bits are covered, including a valid-payload negative control. See
`consumer_closure.py`, `consumer_closure_review.md`, and
[`results/consumer_closure_v3/summary.json`](results/consumer_closure_v3/summary.json).
This closes the consumer projection, not the candidate producer proof.

## Proof reductions and recorded outcome

The existing correspondence matcher found zero register pairs after
`async2sync`, because native Q names became reset-mux outputs. The proof-local
helper instead finds 1,773 native matches before lowering. It excludes every
ambiguous shared-bank alias: the first candidate leaves 1,645 unchanged pairs
and omits 128 original operand/result bits. Equality certificates are additional
assertions, never state assumptions.

A generic last-writer monitor asserts that the shared bank equals the original
bank whose actual write-enable fired most recently. It uses no hand-written
instruction-phase predicate. Certified common-state factoring keeps the
reference's actual state evolution, shares only matched candidate Q values,
and asserts equality of both original effective next-state expressions,
including enable and reset. Direct, defined native reset values establish the
base case. This made the identity proof complete in 0.01 seconds.

The final proof-only abstraction replaces the ALU result with coherent symbolic
values: equality of the **complete** 132-bit control/operand tuples permits one
shared result; unequal tuples permit independent results. Structural cone
identity and an undefined-value SAT check establish that both original cones
are the same total combinational function. The actual output is defined for
all defined input tuples, including defaults. This is an overapproximation
of the original paired RTL, with no input-equality assumption or hardware edit.

| Check | Outcome |
|---|---|
| Compatible pairs / exclusive-write survivors | 276 / 16 |
| Full ROB and smaller ALU+CDB plain identities | Both unknown at 120 s |
| Factored identity; coherent identity | Both proved |
| Native, last-writer, factored, coherent candidate attempts | Each unknown at 120 s |
| Final coherent candidate | Frame 4; no counterexample; no accepted rewrite |
| Raw local ALU payload observation attempt | Unknown at 60 s; not labelled a counterexample |

Independent small-model tests cover positive sharing, overlapping live values,
wrong writes, ambiguous state aliases, undefined resets, and unequal ALU
control/operand tuples. These validate the mechanisms; they do not replace the
unfinished target proof. See `helper_review.md` and `coherent_alu_review.md`.

## Automatic conditional-invariant experiment

The next bounded experiment discovers predicates from the native write-enable
cones instead of supplying instruction phases. It selected a three-bit control
register, found seven existing predicates, and generated fourteen guarded bank
equalities. BMC rejected seven; the seven survivors remained assertions in the
joint functional proof. Three-step base checks passed, induction failed, and
joint PDR returned `UNDECIDED` at 120 seconds. No survivor is called a proved
LEN5 invariant. A small-model regression does prove automatically selected
guards plus its functional outputs by base and induction.

One final conditional run added a proof-only bitmap tracking destination tags
from accepted ALU issue through local ALU CDB completion. It assumes no reuse
of an outstanding tag, permits same-edge release/reallocation, and clears on
native reset/flush. This adds exactly one assumption, for two total with the
initial-reset premise. Payloads, backpressure, and operand readiness stay
arbitrary. It also returned `UNDECIDED` at 120 seconds. The actual ROB/issue
context has **not** been proved to satisfy this premise; any conditional proof
would remain intermediate until that closure is established.

The standalone protocol negative produced an explicit duplicate-allocation
counterexample. A separate native two-copy duplicate-tag stress screen found
no functional mismatch through 12,864 cycles and was stopped; this is
inconclusive. The induction traces point to missing relations between retained
arbiter requests and row states. See `guard_protocol_review.md` and
[`results/guard_protocol_v1/summary.json`](results/guard_protocol_v1/summary.json).
There are still zero accepted target rewrites and no mapped-area result.

## Reproduction in fresh directories

Run from the code-repository root. Build directories below are examples and
must not already exist. The default dependencies are the existing clean LEN5
checkout and the pinned local OSS CAD Suite.

```sh
python experiments/bounded_dynamic/len5/phase_sharing/prepare.py \
  --boundary alu_cdb --output /tmp/len5-phase-baseline
python experiments/bounded_dynamic/len5/phase_sharing/run.py \
  --baseline /tmp/len5-phase-baseline/baseline.json \
  --output /tmp/len5-phase-proof --proof-mode coherent \
  --timeout 120 --max-candidates 1
```

The driver requires the source-bound consumer-closure summary, and archives
the exact proof helpers. `--proof-mode plain`, `native`, and `factored` retain
the earlier proof strategies explicitly. To retain all ROB consumers directly,
use `--boundary alu_cdb_rob` in preparation.
`--raw-cdb` prepares a separately labelled raw-payload observation control;
`--wrong-data` invokes the explicit bad rewrite. The driver archives the exact
bank-sharing and temporal-proof implementations with each fresh run. `negative.py`
provides the separate functional-only wrong-data/raw-local-output controls.

To reproduce the guard/protocol experiment from its archived original proof
model, use fresh directories. The source model retains the unchanged native
reset premise and all prior proof obligations.

```sh
mkdir /tmp/len5-guard-source
gzip -dc experiments/bounded_dynamic/len5/phase_sharing/results/guard_protocol_v1/source_model/native.json.gz \
  > /tmp/len5-guard-source/native.json
cp experiments/bounded_dynamic/len5/phase_sharing/results/guard_protocol_v1/source_model/proof.json \
  /tmp/len5-guard-source/proof.json
python experiments/bounded_dynamic/len5/phase_sharing/guard_invariants.py \
  --source-proof /tmp/len5-guard-source --output /tmp/len5-guard-screen \
  --bmc-depth 14 --depth 3 --timeout 120
python experiments/bounded_dynamic/len5/phase_sharing/guard_invariants.py \
  --source-proof /tmp/len5-guard-source --resume-screen /tmp/len5-guard-screen \
  --output /tmp/len5-guard-joint --depth 3 --timeout 120
python experiments/bounded_dynamic/len5/phase_sharing/conditional_protocol.py \
  --source-native /tmp/len5-guard-joint/joint/native.json \
  --output /tmp/len5-conditional-tags --timeout 120
```

The storage ceilings from source inspection are 512 bits for the eight ALU
entries and 1,024 bits across the default ALU/MUL/DIV entries. These are not
mapped-area reductions. The whole-core physical baseline is measured
separately, and any later area claim must use an identical native hardware
mapping flow without formal monitors or arbitrary-initial-state machinery.
