# Independent admission-screen review

Reviewed immutable `streaming_alphabet_gap2_v2` and `v3` source snapshots and the
padded `streaming_fetchgap2_v2` native trace. This is an audit, not a new simulator,
proof run, or accepted optimization. The root-owned formal runner was not edited.

## Findings

**The v2 instruction-service model was not a justified overapproximation of
the native platform.** Its grant was determined by an abstract two-entry queue
and its ages advanced independently of downstream readiness. Native
`memory_bare_emu.sv:345-372,382-395`, with `SKIP_INS_ANS_REG=1`, advances both
instruction stages only when the core's `instr_rready_o` is high; that same
ready drives memory grant through the external spacing gate. Native flush
clears instruction stages at the edge, without combinationally masking their
current valid output. Concrete mismatches: at native active cycle10 request=1,
grant=0, response-ready=0, whereas v2 forces grant1 from an empty queue; at
cycles37 and927 native response-valid=1 on flush while v2 forces it0. v2 never
reached PDR because export failed/timed out; it supplies no safety result.

**The v3 fetch recurrence corrects those mismatches.** It uses the original
two-stage shift/freeze behavior, couples grant to response-ready and gate-open,
retains cooldown across flush, and gives flush priority only at the update
edge. Even an accepted request on a flush edge updates the bandwidth cooldown
while the instruction is discarded. The source-level minimum response latency
is two rising-edge intervals, possibly longer when response-ready freezes the
pipeline. It is not an unconditional two-cycle deadline. The data pipeline's
three stages give a three-edge response interval and are not cleared by flush.

The [trace recurrence audit](formal_screen_v3_trace_audit.json) finds **zero
mismatches across 983 active edges after the first reset** for fetch grant and
response-valid, load grant and response-valid, and every valid load response
tag. All returned fetch addresses are the 14 instruction addresses 0..0x34.
The native trace has 484 completed fetch replies of latency2 and 65 completed
load replies of latency3, with no fetch/load faults. The 128-byte input padding
maps the observed speculative read beyond the last application element. This
is finite trace inclusion evidence; padding alone is not a universal address
safety invariant.

**Remaining exact-payload issue: successful native responses use exception
code `E_UNKNOWN=5'h1f`, while v3 drives0.** Fetch memory initializes this field
to31, and so do native load/store responses. Fetch's code is ignored when its
exception flag is false (`issue_stage.sv:309`); load saves the memory code only
for `LOAD_OP_MEM_EXCEPT` (`load_buffer.sv:346-349`). However,
`store_buffer.sv:358-360` saves the code unconditionally on `STORE_OP_SAVE_MEM`,
and `rob.sv:119-125,156` compares retained codes against misprediction0x18 even
with the exception flag false. Both0 and31 are different from0x18, so the source
suggests the admission control is unchanged; no formal noninterference proof
for this substitution was run. Drive the native31 in a fresh version to avoid
needing that extra lemma. A raw-state/packet equivalence claim for v3 is false.

The formal model drives data grants low during reset while native ready is high.
The recorded reset cycles have no accepted data requests, and all active-edge
grant comparisons match. The formal domain starts with reset asserted; the
native pre-reset startup row is outside that initial-state convention. The
reset-scoped claim should be explicit rather than calling every initial row an
identical trace. Subsequent resets remain possible in the formal query.

## Source and query correspondence

- `core.json` is exactly the qualified original normalized JSON after removing
  two added output ports. `probe_insert` aliases the original ALU RS `insert`,
  and `probe_index` aliases its original 3-bit `new_idx`. No original cell,
  connection, capacity, input or next-state was modified. The source JSON hash
  matches the previously manifest-bound inventory model
  `eed81f042c055fd218116838f154535efdf2534e6cb78a83aba79a6d58bf4131`.
- The instruction selector contains all 14 encoded words from the actual
  disassembly plus NOP. Choices may change independently at each accepted fetch;
  PC order and ROM address/value correlation are removed. This admits more
  instruction sequences, but retains the explicitly nonfaulting external-memory
  domain. Counterexamples may be impossible in the precise application ROM and
  must not be presented as application bugs without concretization.
- Arbitrary 64-bit load values include the recorded input values. There is no
  assumption about operands, issue rate, dependency depth, RS occupancy or
  allocation indices. Interrupts are disabled and memory exception flags are
  zero; these are explicit environment restrictions, not conclusions.
- `!($initstate) || !rst_ni` is the initial reset premise. The ALU insertion
  prohibition is an assertion. It covers actual pre-admission allocation even
  during flush, which is stronger than post-edge live occupancy. It does not
  subtract a simultaneous removal or infer unused indices from a count bound.
- Load/store response readiness is asserted, never assumed. Both native buffer
  modules assign `mem_ready_o=1` (`load_buffer.sv:409`, `store_buffer.sv:428`),
  supporting the always-advancing data service. Three safety assertions are
  required before export. A completed PDR proof is still required; export,
  a low-occupancy simulation, or bounded UNSAT is not acceptance.
- Reproducibility hardening for a future runner: verify the normalized model
  against its manifest-bound derivation and verify prepared source hashes in
  the runner itself. The current instance passes those checks independently,
  but the runner presently only records its input JSON hash.

## Cheapest next step if proof cost is excessive

v3's direct `aigmap` export is appropriate: it avoids an unnecessary expensive
combinational ABC optimization pass while preserving the same safety problem.
The resulting PDR run reached frame7 but ended undecided after120.30 seconds,
with no reported counterexample. This is neither a proof nor a rejection of
the admission property; it does not authorize storage removal.

If the full query remains too expensive, the first sound abstraction to consider
is a **combinational datapath driver**, such as the native `$mul` product,
replaced by fresh unconstrained values each cycle while retaining its original
pipeline, tags, valid/ready and arbitration. This expands the trace set and
cannot make an invalid safety theorem true, though it can create spurious
counterexamples. Record the exact cut and concretize every counterexample.
It is a proof-only abstraction, not an optimized implementation or a license to
delete its hardware. Do not cut scheduling state, force readiness, assume the
desired occupancy bound, or import unproved fairness/latency lemmas. No such
abstraction was applied in this audit.

## Subsequently authorized optional proof model

The root subsequently authorized implementing, but not independently running,
[abstract_datapath.py](abstract_datapath.py). Its default `alu_mul` mode replaces
exactly the original ALU result64 driver `$procmux$11115.Y` and multiplier final
result64 driver `$procmux$7848.Y` by independent `$anyseq` outputs. It uses the
final 64-bit multiplier result, not the internal 128-bit product discussed above.
The optional `alu_mul_branch_taken` mode also replaces the 1-bit semantic
`res_taken` driver `$procmux$20161.Y`. This relaxes taken-outcome restrictions
(including unconditional-jump cases), so spurious recoveries are possible;
branch-unit valid, tags, state, latency and downstream recovery equations remain
native. Either mode contains every original trace by choosing the original
combinational values at each cycle. A proof is stronger; a counterexample is
not necessarily concrete.

The helper preserves all original ports and net aliases, and all cell objects
outside the exact selected combinational drivers. It rejects mixed/partial
packed outputs, reordered output bits, multiple drivers, state-output/input
intersections, explicit protocol aliases, unsupported source modules and repeat
abstraction. The manifest contains each complete original driver object and
both structural hashes. Construction on the qualified model, input immutability,
repeat rejection and injected duplicate-driver rejection were checked. No new
formal/simulation run was launched by this reviewer. Do not map these symbolic
proof models as hardware or report their reduced cones as area savings.
