# Conditional representation-invariant search

This is a bounded feasibility experiment on the first automatically enumerated
64-bit sharing candidate. It has not accepted a LEN5 rewrite or established an
area saving. It is a program-independent control, not the timing-constrained
storage claim. The source is PRE-FPU LEN5 commit
`14291dcc5bef181085d001c5a29e7f4fc4cbc8e9`.

## Automatic candidate construction

`guard_invariants.py` walks backwards from both original bank write enables,
stops at native register boundaries, and ranks common small control registers
by maximum and then total combinational distance. It takes the closest
register under the explicit search bounds (one control register, at most eight
bits). It enumerates existing one-bit equality/logic-not predicates whose
variable inputs belong to that register and whose constant operands are
defined. It supplies no source field name, enum value, or instruction phase.

For each predicate it asserts both possible representation equalities,
`guard -> reference_A == shared` and `guard -> reference_B == shared`.
These are assertions, never assumptions. Duplicate expressions are removed.
The search chose a three-bit register four and three combinational steps from
the original write enables. Seven existing predicates gave fourteen guards.
BMC through fourteen steps rejected seven. The remaining seven are candidates,
not proved invariants.

The joint proof retains all original functional-output obligations, effective
next-state equality certificates from common-state factoring, and the
last-writer assertion. The original reset premise and coherent-ALU
overapproximation remain unchanged. Joint base checks through three steps
passed; induction failed on a global output and an effective-next-state
obligation. A separate guard-only induction attempt also failed, and joint
PDR returned `UNDECIDED` at 120 seconds. Failed induction describes an arbitrary
induction prestate; it is not a reset-reachable hardware counterexample.

The induction trace exposes stale arbitration masks with no corresponding
ready rows. Native `rr_arbiter.sv:52` selects retained requests before current
requests, and `arith_rs.sv:360-395` retains both execution and CDB selectors.
Phase predicates alone do not establish the reachability relations between
these masks, row states, and observation selection. The next missing argument
is control reachability/ownership, rather than arithmetic equality.

## Explicit conditional tag protocol

`conditional_protocol.py` adds a proof-only 32-bit ownership bitmap. An ALU
issue reserves its destination tag only on issue valid/ready acceptance. The
actual local ALU CDB valid/ready completion releases its tag. Reset and flush
clear the bitmap; same-edge release and reallocation are permitted. One new
assumption forbids allocating an already-owned tag. There are exactly two
assumptions after elaboration: the prior initial-reset premise and ownership.
No operand, readiness, execution-phase, occupancy, or service bound is added.

The binding uses original wrapper interfaces: ALU local valid, raw local CDB
payload tag `[74:70]`, and normal CDB ready slot 2. `expipe_pkg.sv:104-109`
defines the packed CDB tag and payload; its `EU_INT_ALU` value at line 226
places the ALU at normal slot `3-1`. No local payload projection is introduced.
The global consumer-closure proof remains a separate required obligation.

This premise is **not certified on the actual core**. Source inspection makes
the intended ownership mechanism concrete:

- `issue_stage.sv:498` uses the ROB tail as execution destination; the same
  tail is returned by `rob.sv:268`.
- `issue_cu.sv:83,207-211` jointly accepts integer execution and ROB issue only
  when both downstream interfaces are ready.
- `rob.sv:92-103,184-189,267` rejects allocation at a valid tail, advances the
  tail on accepted push, and clears valid on commit.
- `rob.sv:134,152-158` requires result-ready for both commit paths.

A compositional closure still needs to relate ALU issue, ROB ownership, CDB
completion, and tag release through arbitrary flushes and other producers.
In particular, arbitrary external producers at this component boundary may
send unrelated tags; source reading alone does not prove their consistency.
Even a successful conditional component proof would remain intermediate until
that context theorem is proved. No conditional result is used to accept or map
the proposed rewrite.

## Falsifiers and scope

The unconstrained wrapper permits duplicate live destination tags.
`arith_rs.sv:216-227` completes every waiting/requesting row with a matching EU
result tag, while the execution selector removes one served request at a time.
This suggests a possible stale-request failure outside native allocator
ownership. It is a hypothesis, not a confirmed counterexample for the first
candidate. A native two-copy simulation, including eight duplicate-tag rows
and then arbitrary readiness/tag/backpressure/flush events, found no mismatch
through 12,864 compared cycles before the cheap screen was stopped. The first
candidate is row zero, which has first service priority; later rows may have a
different failure mode. No conclusion is inferred from the absence of a trace.

The conditional runner also checks the protocol monitor alone with its
ownership assumption changed to an assertion. A duplicate allocation without
release must produce an explicit finite counterexample. That validates the
monitor's rejection behavior; it is not a bank-rewrite counterexample.

All target outcomes, failed guards, induction traces, exact scripts/models,
and the native screen are retained separately. The small-model test proves an
automatically selected guarded representation relation by base plus temporal
induction, demonstrating that the generic mechanism works on a tractable
control example. It does not replace the unfinished LEN5 proof.
