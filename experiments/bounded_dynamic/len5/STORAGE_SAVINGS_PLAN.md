# Screened plan: substantial storage removal in unchanged LEN5

This supersedes the small-tag direction as the main experiment. The RSD result
remains a mechanism check, not a proposed paper payoff. This document reports
source review, a cheap structural inventory, and the subsequently authorized
DIV and streaming-kernel counterexamples below. No occupancy invariant or
storage-removal transformation has been certified. The structural counts are
separate from physical mapping results.

## Research comparison: information versus optimization method

The research hypothesis is that Pscorr can turn program and microarchitectural
facts into ODC-based hardware savings. Program/ISA-driven whole-core savings are
already a Pscorr contribution; they are not credited to an unrelated competitor.
The key ablation is **Pscorr with ISA/program constraints versus Pscorr with the
same constraints plus microarchitectural/timing information**. The extension's
payoff is the additional saving, while the paper credits Pscorr for both stages.
Do not presuppose that an ISA-only baseline saves little. Instruction restrictions
can already remove substantial functional units, and an ISA constraint can itself
create a microarchitectural ODC. The information supplied and the optimizer's
ability to exploit that information are separate experimental variables.

Measure a strong ISA/program-constrained Pscorr baseline and its timing-enhanced
version under the same
program, external platform, reset, observation boundary, capacities, mapping and
resource budget. Separately ablate scheduling/timing information in Pscorr while
keeping the instruction restrictions fixed. Give the existing sequential
optimizer the complete constraints as an additional control: its result tests
whether the gain follows from extra information alone or requires ODC discovery
and rewriting. A method that already uses internal temporal reachability should
not be relabeled "ISA-only" merely because its input constraints mention ISA
instructions.

Report total whole-core area and the incremental reduction from the strong
ISA/program baseline to the microarchitecture-aware result, with each new
removal tied to a certificate and a matched timing ablation. Formal-monitor or
encoded AIG area is not a native implementation baseline. A small or negative
increment is a legitimate experimental outcome; it does not justify weakening
the baseline. No result currently establishes that ISA-only savings are small
or that a material additional whole-core saving has been obtained.

For original area `A0`, ISA/program-constrained Pscorr area `AI`, and
timing-enhanced Pscorr area `AM`, report `(A0-AI)/A0` as the first Pscorr gain,
`(AI-AM)/AI` as the additional relative gain, and `(A0-AM)/A0` as the combined
gain. Additional percentage points relative to the original core use `A0` as
their denominator and must be labeled separately.

The measured 12.40% result uses an exact instruction alphabet in arbitrary
order, whereas the current admission query also uses an address-indexed ROM.
These differ in program information as well as timing. Before attributing a
later area increment to timing, add a matched exact-ROM/program-only baseline
and hold the ROM, fault policy, decoder, reset, data service, observation,
candidate search, mapping, and resource budget fixed while varying the fetch
spacing information. The intended attribution is alphabet specialization,
then any additional ROM/program-only specialization, then the timing increment.
The current 12.40% is not an upper bound on program-only Pscorr.

For an individual storage row, a feasible gap1 admission witness together with
a closed gap2 no-admission proof and accepted replacement demonstrates timing
dependence. The matched native witnesses already cover rows 1, 2, and 3; they
do not establish timing dependence for row 0. Keep any row-0 saving separate
until its matched control is resolved. This prevents crediting a gain from
more precise program information to timing.

## Current screening outcome

The [padded streaming experiment](application_screen/FETCH_SPACING.md) checks all
64 output values on the unchanged core. Native service allocates ALU slots 1–7;
the external minimum-two-cycle fetch-spacing platform allocates slots 5–7 and
retains actual out-of-order issue. Both have three-cycle load responses and no
memory exceptions. The platform changes reported execution from 805 to 931 cycles;
all optimizer comparisons must use the same chosen platform. A trace visiting
fewer slots is a candidate-discovery observation, not a removal certificate.

The [alphabet-domain formal screen](application_screen/evidence/formal_screen_v5/README.md)
does not yet certify the application. Unbounded checking remains inconclusive.
A bounded query finds an ALU admission violation at frame 19 after proof-only
ALU/MUL result abstraction. Its external input prefix has now been
[concretized in the original native RTL](application_screen/evidence/native_concretization_observed_v1/summary.json):
the core uses a fifth distinct ALU slot even though current occupancy never
exceeds four. Simultaneous insertion and completion cannot reuse the completing
slot on that edge. This rejects the proposed four-slot admission bound for the
alphabet platform. The alphabet environment is broader than the actual program,
so it does not reject the same query for the address-indexed streaming ROM.

The [executable-ROM platform](program_platform/README.md) now derives immutable
instruction bytes from ELF executable sections, independently of data RAM.
Its unchanged 56-byte program checks all 64 output stores and retains 64 actual
out-of-order issue inversions. Every core source file and declared capacity is
unchanged. The external platform explicitly returns zero payload on instruction
faults and preserves the original fetch/data pipelines. This is a declared
Harvard platform, not a universal equivalence claim about unified memory.

The [matched Harvard fetch-spacing ablation](program_platform/GAP_ABLATION.md)
now reproduces the 805/931-cycle comparison with identical ELF, executable ROM,
data, core sources, and memory implementation. Native gap1 admits ALU rows 1–7;
gap2 observes only rows 5–7. The gap1 admissions to rows 3, 2, and 1 precede its
single speculative instruction fault, whose payload is zero as specified.
This is a concrete negative control for excluding those rows without the gate;
finite absence under gap2 still requires an unbounded proof.

Matched JSON-flow synthesis measures original whole-core area 1,400,805.984,
Pscorr instruction-operation specialization 1,306,082.637 (6.76% less), exact-word
decoder specialization 1,300,886.403 (7.13% less), and the cumulative program-only
decoder/register specialization 1,227,165.699 (12.40% less). These numbers must
not be divided by the separate RTLIL-flow denominator below. The program-only
gain is a Pscorr contribution. Its [cumulative certificate](isa_baseline/results/program_registers_certificate_v2.json)
binds corrected symbolic-undefined-value proofs, native domain propagation,
and complete component-consumer closure. Its instruction premise applies only
while reset is released and the external response is valid; it introduces no
timing or occupancy premise. Earlier certificates withdrawn during that audit
remain archived. No larger timing-derived saving has yet been certified.

The [RF composition audit](application_screen/review/rf_composition_v1/README.md)
replays the cumulative certificate exactly and confirms complete RF consumer
coverage and unchanged ALU admission/row state outside that component. Under
the same initial-reset and program-response premises, an eventual admission
theorem transfers from the decoder-only native core to the cumulative RF
candidate. Apply any accepted ALU-row patch to that cumulative candidate
(`371a91db44e992635c234ba339907654b62a6800c43d787561cea2bbbbe67b7e`), so RF savings
are not counted a second time. The admission theorem and row-removal
justification are still required; the composition audit supplies neither.

The scheduling query now composes an independently proved external ROM domain
with seven source-bound native instruction-word invariants. These are proved
conclusions reused by the checker, not guessed internal occupancy assumptions.
Native-arithmetic and payload-abstracted PDR runs remain unknown at 120 seconds;
their bounded searches did not complete the requested 64 frames. The optional
branch abstraction has been prepared and reviewed but not solved. All native
hardware exports remain identical; smaller proof models are not hardware gains.
See [the source-bound query record](application_screen/README.md#source-bound-instruction-domain-lemmas).

Two further solver diagnostics also remain inconclusive. The word-level MBIC3
query timed out at 120 seconds. Gate abstraction reduced the ALU/MUL proof model
from 22,725 latches and 530,756 AND nodes to 491 latches and 9,650 AND nodes;
explicit PDR on that abstraction still timed out at 120 seconds without a
counterexample. These are verification-model reductions, not hardware savings.
The [solver records](application_screen/GATE_SOLVER.md) preserve the original
constraints, validation cases, dependencies, and unknown verdicts. These short
runs do not establish whether a 24-hour run would finish.

A subsequent [bounded diagnostic](application_screen/GATE_BMC.md) found and
validated a frame-25 counterexample in the 491-latch abstraction in 8.05 seconds.
That abstraction cannot prove the safety property without refinement. This does
not refute the original proof model or native RTL: its extra free choices must
first be checked for feasibility in those models. Extending PDR on this exact
abstract model would therefore not establish the desired safety theorem.

A [600-second continuation of normal gate abstraction](application_screen/GATE_RESUME.md)
reused the saved refinement map, rechecked from frame zero, and advanced beyond
that failure. It remained unknown at timeout in frame 32, with no validated
original-model counterexample or unbounded proof. Separately, the
[native-arithmetic preparation](application_screen/NATIVE_ARITHMETIC_PREPARATION.md)
retains exact loop-counter and pointer computations after the closed inactive-FU
substitutions. It has 522,336 AND nodes and 22,024 latches, compared with 493,830
and 20,968 for the corresponding payload-abstracted model. These remain proof
model counts, not hardware savings.
Its [first 600-second GLA run](application_screen/NATIVE_GATE_SOLVER.md) also
remained unknown, timing out in frame 29 without a proof-thread call or a
validated counterexample. The retained 684-latch abstraction is diagnostic
evidence only.
A subsequent [bounded check](application_screen/NATIVE_GATE_BMC.md) validated
a frame-29 counterexample in that abstraction in 63.016 seconds. It has not
been concretized against the native query. Direct PDR on this unchanged map
cannot establish safety; further work must refine the abstraction or prove
additional native invariants, rather than treat the timeout as a certificate.

The next proof simplification follows a closed program-only chain: the certified
decoder excludes MUL/DIV dispatch, the native issue register preserves that
exclusion, and the original insertion gates therefore never admit either unit.
All eight MUL/DIV row reset invariants pass base and induction; removing the
local no-admission premise gives a counterexample for each row. This supports
1,761 exact constant-state substitutions in a separate proof query, with native
hardware unchanged. The [source-bound record](application_screen/INACTIVE_FU_LEMMAS.md)
does not discharge the ALU-row admission obligation or establish a timing gain.

The [automatic reset-storage preparation](application_screen/RESET_STORAGE.md)
proves a conditional native theorem for every ALU RS row: if it receives no
admission while reset is released, its 220 raw state/payload FF bits remain at
their reset values. Each theorem has a counterexample when that premise is
removed. The generator derives constant-state patches from the original FF
drivers without changing capacity parameters. No patch is an accepted core
rewrite until the whole-core admission theorem discharges its premise; no
additional mapped-area result is claimed from these local proofs.

The [program-independent phase-sharing control](phase_sharing/README.md) enumerates
276 bank pairs and retains 16 after a necessary write-exclusion check. No target
bank merge has an unbounded certificate. A common-state proof reduction makes
identity checking fast and passes independent positive/negative tests, but that
does not prove the proposed merge. No transformed whole-core area has been
measured for that sharing candidate. Automatic phase guards and an explicitly
conditional unique-tag protocol still leave its proof inconclusive; neither
becomes an assumed native-core invariant. The next substantive obligations are
certifying the actual program/platform admission property and measuring
additional native whole-core savings against the certified program baseline
before attributing an incremental timing benefit.

## 1. Settings and source-grounded inventory

The target is the qualified official pre-FPU commit
[`14291dcc5bef181085d001c5a29e7f4fc4cbc8e9`](https://github.com/edge-group-polito/len5/tree/14291dcc5bef181085d001c5a29e7f4fc4cbc8e9),
not the current FPU revision. All 74 selected core files remain byte-identical
to that commit. ROB32, IQ4, LB8, SB16, ALU RS8, MUL RS4 and DIV RS4 stay fixed.
One ranked idea is proposed: automatically prove unused arithmetic RS entries
and eliminate their storage with full consumer closure. The initial falsifier
budget should be two hours; a surviving first unbounded certificate gets one
day before reassessment. Existing tools suffice; no FPGA or new core is needed.

The structural result is [results/storage_inventory.json](results/storage_inventory.json),
generated by [storage_inventory.py](storage_inventory.py). Reading the certified
RTLIL and applying ordinary word-level `opt` gives **24,089 unique FF Q bits**,
down from 24,157 before that cleanup. These are not physical cells or area.
The cleanup uses no service assumptions and no Pscorr rewrite.

The separately measured unchanged-core mapping is
[results/native_area_v1/summary.json](results/native_area_v1/summary.json):
1,405,010.016 square micrometers of library cell area and 23,734 physical FF
cells (23,196 reset FFs, 24 set FFs and 514 enable FFs). This is a native-hardware
baseline with no optimization or layout/timing claim. It supplies a whole-core
denominator; the unmapped payload counts below are not area estimates.

| Bank | Entries | Payload FF bits after ordinary opt | Allocation/access | Source under `rtl/` |
| --- | ---: | ---: | --- | --- |
| ROB | 32 | 5,632 | Rotating tail | `expipe/commit-unit/rob.sv:92-105,220-254` |
| Store buffer | 16 | 3,472 | Rotating tail; completed payload retained for forwarding | `expipe/load-store-unit/store_buffer.sv:174-183,288-297,377-425` |
| Integer RF | 31 stored registers | 1,984 | Architectural register index | `expipe/register-file/int_rf.sv` |
| BTB | 16 | 1,936 | PC indexed | `frontend/btb.sv` |
| ALU RS | 8 | 1,728 | **Highest-index free first** | `expipe/exec-units/arith_rs.sv:350-357` |
| Load buffer | 8 | 1,696 | Rotating tail | `expipe/load-store-unit/load_buffer.sv:153-174` |
| Branch RS | 4 | 1,368 | **Rotating tail**, not first-free | `expipe/exec-units/branch_rs.sv:130-140,310-345` |
| Multiply RS | 4 | 852 | **Highest-index free first** | `expipe/exec-units/mult_unit.sv:130-178`; same `arith_rs` |
| Divide RS | 4 | 852 | **Highest-index free first** | `expipe/exec-units/div_unit.sv:61-96`; same `arith_rs` |
| Predispatch IQ | 4 | 668 | Rotating FIFO | `expipe/issue-unit/issue_queue.sv` |
| RAS | 8 | 512 | Stack pointer | `frontend/ras.sv` |
| Fetch prediction FIFO | 2 | 260 | Rotating FIFO | `frontend/fetch_mem_if.sv:97-114` |

Other state, including CSRs, bank control, instruction/commit registers and
functional-unit pipelines, accounts for the remaining bits. Payload-bank sets
are checked disjoint, avoiding double-counting aliases of the same Q bit.

**Allocator polarity is decisive.** `arith_rs` instantiates `prio_enc` without
overriding `INV`; its default is zero. `common/prio_enc.sv:54-65` scans index 0
upward and retains the last asserted input. Fresh allocation therefore starts
at 7 for ALU, or 3 for MUL/DIV, and descends as those entries fill. Low-index
entries are the candidates for being unused. Execution and CDB selections use
separate round-robin arbiters; those do not make allocation circular.

The first-free payload pool is **3,432 bits, 14.25% of the unmapped core FF bits**.
This gives a credible storage ceiling and a warning against unlimited payoff
claims. Hypothetical removal of four ALU entries and two MUL entries targets
`4*216 + 2*213 = 1,290` payload FF bits, plus associated control; six ALU and
three MUL entries would target 1,935 payload bits. These are arithmetic estimates
conditional on proofs, not predicted mapped-area percentages. If DIV is excluded
by an instruction contract, its 852 bits are not part of the timing benefit.
The multiply datapath and other combinational logic also affect whole-core area.

## 2. Ranked idea card

### A. Title: Prove unused first-free arithmetic reservation storage

**B. Falsifiable hypothesis.** A defensible positive-latency instruction/data
service contract, combined with an explicit integer instruction domain, leaves
at least four low ALU RS entries and two low multiply RS entries never allocated
in this unchanged core. Generic state/driver candidates can then remove at least
roughly 1,000 payload FF bits while preserving genuine OoO execution and every
functional whole-core observation.

**C. Novelty claim.** Relative to the present equality-width enumerator, the
extension is automatic grouped state/payload candidate discovery with certified
consumer closure and composition. The bound is proved from real execution
events, not copied from a trace or assumed as occupancy. Literature novelty of
state-liveness optimization is unverified (CITATION NEEDED); do not claim that
the occupancy formula or first-free allocation is new.

**D. Why it matters.** This targets kilobits of stored operands and results,
including their update and selection logic, rather than another two-bit tag
change. It implements the original bounded dynamic scheduling idea on a genuine
OoO core while retaining the original declared capacities.

**E. Comparisons.** Keep three distinctions explicit:

1. An ISA/program-constrained Pscorr baseline and its timing-enhanced run use the exact same
   instruction restrictions. Excluded DIV/REM hardware or unused instruction
   fields cannot be counted as timing-derived storage savings.
2. Inherited Pscorr/scorr and the proposed state-candidate method receive the
   same complete contract, reset semantics, observations and resource budget.
3. The final physical comparison uses native hardware only, identical mapping
   settings, and the complete core. A large RS-block percentage alone is not
   the desired outcome; formal monitor/AIG state is excluded.

**F. Key assumptions to screen, not silently accept.**

- The first positive candidate domain excludes DIV/REM encodings but retains
  loads, stores, branches, general integer ALU and multiply. This restriction
  applies to actual fetched/issued instructions, including wrong-path work,
  and is identical in the ISA-only baseline. Do not change `LEN5_DIV_EN`.
- Start with a concrete nonzero platform profile: accepted instruction reads
  at least two cycles apart, ordered instruction response at three cycles,
  at most two pending instruction reads; asserted data requests accepted within
  one cycle and their tagged responses delivered within one to four cycles.
  Include stores, not only loads. Define exact edge conventions before proving.
  This is a proposed bandwidth/latency domain, not a property of all memories.
- Retain recovery, exceptions and the native treatment of already-issued data
  responses across flush. Instruction responses must use the existing compatible
  positive-latency protocol with FIFO2, not the failed zero-stage configuration.
- Do not assume operand readiness, RS occupancy, issue spacing, CDB grant
  fairness, maximum dependency depth, or unreachable entry indices internally.
  If needed, prove those as consequences of the actual core and external domain.
- Before selecting a final domain, check representative real integer kernels
  against these instruction/timing premises and retain a dynamic issue witness.
  If the profile eliminates all waiting/bypass behavior, reject it as the main case.

**G. How this dies: actual source-level obstacles.**

1. **DIV defeats a memory-only lifetime argument.** `div_unit.sv:61-96` uses a
   four-entry arithmetic RS; `serdiv.sv:155-218` iterates a data-dependent counter.
   One long divide followed by eight independent-destination ALU consumers of
   its result fills ALU RS8 even with fast memory in the executed
   [counterexample](results/div_falsifier_v1/summary.json). Keeping full RV64IM requires
   a real bound on DIV placement/consumption, not merely a memory deadline.
2. **MUL is not absent or combinational by assumption.** Its default is the
   parallel unit with an input register; `mult.sv:130-250` and
   `mult_unit.sv:167-178` determine the actual result latency. `PIPE_DEPTH=1`
   alone is not a sufficient lifecycle bound. Result/CDB congestion still matters.
3. **Operand chains are part of residence.** `arith_rs.sv:161-214` admits
   instructions with one or both operands pending. Short accepted-request-to-
   response latency does not bound time before a load's address/request is ready,
   or before a store dependency clears. A grant bound is needed in addition to
   a response bound, but even those do not erase instruction dependencies.
4. **CDB fairness is not a label.** The highest-priority source is the store
   buffer (`expipe_pkg.sv:223`, `backend.sv:443-448`). Other units can be delayed
   by store completions. The ROB is always CDB-ready (`rob.sv:264`), so the cause
   is not arbitrary ROB backpressure. `cdb_arbiter.sv:69-93` and the local
   `rr_arbiter.sv:77,102-112` must be analyzed together: local selection masks
   advance even without an actual downstream grant. Do not assert a guessed
   “one service every N cycles” bound or claim starvation from that detail alone.
5. **Fetch spacing is not dispatch spacing.** IQ4, the prediction/answer buffers,
   and the issue register can accumulate and later release a burst. Prove an
   arrival curve at actual `insert`, or directly prove the low-entry property;
   dividing a lifetime by external fetch spacing is not sufficient.
6. **Post-cycle occupancy is insufficient.** `new_sel` sees current empty bits.
   An entry removed on this edge is not available to the simultaneous insertion.
   A design whose occupancy never exceeds K can still allocate outside the K
   highest slots on a simultaneous insert/remove. Use pre-admission state.
7. **Empty state is not payload zero.** `arith_rs.sv:239-243` clears state on
   flush, but its payload update at249 onward only resets on reset and still
   executes `arith_op` during flush. A never-live entry can receive a write on
   a flush edge. Prove write exclusion too, or prove that all future payload
   consumers are masked in the full core. Do not add an output mask to pass proof.
8. **The largest banks rotate.** ROB, branch RS, LB and SB can visit every slot
   at low occupancy. SB also retains CACHED data for future forwarding after a
   store completes. No lifetime bound licenses deleting arbitrary numeric slots
   from these banks; no capacity edit or allocator replacement is proposed.

**H. Cheapest decisive tests, in this order.**

The initial tests are falsifiers on the original complete core or a faithfully
connected actual-RTL cone. They must not start by implementing a “reduced RS.”

| Query | Concrete event/condition | Decision |
| --- | --- | --- |
| Memory-only negative | Full integer domain, fast memory; cover ALU `insert && new_idx==0` with a long divide producer and its consumers | Completed: all eight entries simultaneously RS1_PENDING; memory-only premise rejected |
| Main ALU screen | Candidate matched no-DIV domain and stated nonzero platform profile; cover `insert && new_idx<4` for ALU RS8 | Any legal trace rejects the four-entry removal target |
| Main MUL screen | Identical domain; cover MUL `insert && new_idx<2` | Any legal trace rejects the two-entry removal target |
| Flush-write screen | For every proposed dead entry, cover non-NONE `arith_op[i]`, including flush edges, even if `curr_state[i]` stays EMPTY | Determines whether zero substitution is justified or consumer-sensitive ODC is required |
| Genuine OoO cover | Older load-dependent arithmetic remains pending while a younger independent arithmetic instruction is accepted by its EU | Must remain reachable in the positive domain |
| Timing ablation | Keep the exact ISA/instruction restrictions, relax request grant or response deadline and repeat allocation covers | At least the claimed timing-dependent dead state must become reachable or the attribution needs revision |

Use a bounded search of roughly 64–96 cycles for the falsifier screen, with a
strict wall-clock budget; a counterexample is decisive. Bounded UNSAT is only
permission to try induction/PDR, never authority to remove storage. Preserve
all actual dispatches, not just retired instructions. Check observed trace
events against source handshakes and reject infeasible abstraction traces.

The completed DIV challenge uses [run_div_falsifier.py](run_div_falsifier.py)
and the already qualified simulator binary, without rebuilding or changing any
core RTL. The input program first loads its divisor from memory, then executes
one `divu` and eight dependent `addi` instructions. The actual memory response
arrives three cycles after its request. At VCD time 59 (pre-edge cycle 29), an
insertion into index 0 changes live occupancy from seven to eight; all eight
post-edge states are `RS1_PENDING`. The program checks the quotient and all
eight results and exits zero. The original simulator binary/source hashes,
fresh-run commands, assembly, selected raw VCD, and occupancy trace are retained
in [results/div_falsifier_v1](results/div_falsifier_v1). This is an observed
falsifier of a memory-only storage bound, not an optimization result or an
unbounded proof.

The parent agent's subsequent
[64-element streaming increment](results/streaming_v1/summary.json) also rejects
the four-entry ALU target under the native fast-memory model, without using DIV.
It checks all 64 accepted output stores plus the exit store and exits zero.
The unchanged core reaches six live ALU entries (first at pre-edge cycle85),
including an insertion into index2. Over the run seven distinct slots are used.
Thus even this ordinary no-DIV kernel does not justify retaining only the four
highest slots. This run does not implement the proposed two-cycle accepted-fetch
spacing contract; a separately authorized screen is needed before judging that
more restrictive profile. No timing restriction may be inferred from this
passing architectural trace alone.

For a positive result, require unbounded properties on the original RTL:

```text
ALU: insert -> new_idx >= 4
MUL: insert -> new_idx >= 2
each proposed dead entry: curr_state[i] == EMPTY
plus either: its original write driver is never active
or: the proposed storage substitution is unobservable at every full-core output
```

An explanatory pre-admission theorem may be `insert -> live_count < K`; do not
subtract a same-cycle removal from `live_count`. If residence ends at an edge
exactly T cycles after insertion, a periodic arrival argument must include the
entry removed at that edge. For example, at spacing D with T divisible by D,
K may need `T/D + 1`, not `ceil(T/D)`, because of the allocator's no-same-edge reuse.
Prefer direct RTL predicates over an informal formula when proving the candidate.

Only after this screen, extend Pscorr to enumerate grouped state/driver
substitutions over all entries of the selected first-free banks. Prove each
candidate and the final composition with unchanged observations, then let normal
synthesis delete constant/dead FFs and their cones. No entry-count parameter is
changed, and the tool must discover which indices survive. A local payload
proof may explain the result but cannot replace the final full-core certificate.

**I. Stop and pivot rules.**

- Stop the main positive profile if allocation covers reach the target low
  entries; inspect the cause before considering one justified contract revision.
  Do not run an unbounded grid of increasingly restrictive timing assumptions.
- If success requires a special software instruction pattern, establish it from
  actual kernels first. A class-spacing or bounded-fanout instruction condition
  is permissible only as an explicit monitored domain shared by the baseline,
  never an invented internal ready/occupancy assumption.
- Keep the first substantial-storage gate at roughly **1,000 certified payload
  bits** before spending on full physical evaluation. As a proposed final payoff
  gate, require at least **5% whole-core mapped area** at unchanged observations
  and no change to the compared cycle traces; this threshold is a research
  decision, not a predicted result. If the user/root chooses a higher bar, use it.
- If first-free storage cannot meet that bar, do not return to small tag cuts.
  A different core with larger first-free banks may be a cheaper pivot than a
  new automatic lifetime-based storage-sharing transformation for rotating ROB
  slots. The latter could target the larger ROB bank but is a separate major
  algorithm with alias/write arbitration proof obligations, not manual resizing.

**J. Week-one plan.**

1. Select and document one meaningful ISA/platform domain; demonstrate its
   nonempty kernel/OoO behavior before trusting an abstract constraint set.
2. Retain the completed DIV/streaming challenges, then run the actual
   low-entry/flush-write covers in the selected platform domain.
3. Seek one unbounded low-entry proof; terminate the profile if it cannot be
   certified within the agreed budget.
4. Add generic grouped state candidates, exact driver replacement and composition
   proof, reusing existing fail-closed provenance and mapping infrastructure.
5. Evaluate complete-core area against the same ISA-only baseline and matched
   inherited method, plus architectural/cycle tests and timing-relaxation negatives.

**K. Risk and confidence.** Technical risk is high until lifecycle and arbitration
bounds are proved; execution risk is medium given the qualified small core;
literature novelty risk is medium. Confidence in the cheap negative screens is
high. Confidence in achieving the proposed whole-core area gate is currently low:
the inventory establishes opportunity size, not reachability or mapped savings.

## 3. Go/no-go summary

Go only on the source-correct highest-free ALU/MUL storage screen. First prove
the actual low-entry predicates and payload consumer closure under a defensible
nonzero service domain. The unconstrained-DIV memory-only argument is already
rejected, and native fast-memory streaming also reaches below the four-slot target.
Do not target rotating ROB/LB/SB/branch slots with a count bound. The largest
missing fact is an externally implied bound on **allocation-to-CDB-removal
residence**, including operand waits, buffered arrivals, store-priority CDB
interference and same-edge allocation semantics.

## 4. Verification pass and inventory reproduction

The proposal has a measurable storage/whole-core payoff gate, explicit matched
baselines, positive-latency contracts, concrete original-RTL falsifiers, and
unbounded-proof/negative-control requirements. Its key uncertainty is explicit:
no proposed K, deadline or area gain has been proved. Source paths above refer
only to the qualified pre-FPU commit. No capacities or core sources were edited.

The structural model was exported from the manifest-bound `normalized.il` by
`read_rtlil; write_json`; a separate copy received only `opt; stat; write_json`.
Both commands and inputs are recorded under the outer workspace's
`experiments/bounded_dynamic/len5/build/storage_inventory/`. With those inputs:

```sh
python3 experiments/bounded_dynamic/len5/storage_inventory.py
```

This regenerates only the compact count/hash report. It does not launch a proof,
simulation, technology map, or timing-optimization experiment.
