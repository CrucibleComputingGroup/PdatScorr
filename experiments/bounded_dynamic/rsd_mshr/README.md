# Timing-dependent tag ODC in original RSD components

This experiment uses the original two-entry RSD miss handler, its memory-port
arbiter and multiplexer, the original instruction/data memory-access controller,
and the original four-entry read-ID free list. The source is pinned to RSD commit
`7b65f6ba0bce58d4d859082660123b7100aae975`. No capacity, source-level comparator,
admission gate, or reset behavior is changed in the final `baseline_v5`.
Earlier `baseline_v3/v4` wrappers had an additional external read-stall input;
they are retained as historical models and are not the final native composition.

The intended automatic optimization removes redundant bits from equality cells
in the flattened hardware, subject to sequential equivalence under an external
read-service contract. The local proof here explains the opportunity and tests
the contract. It is separate from the generic candidate generator and its
two-copy equivalence proof; it does not supply assumptions about the desired
rewrite to that proof.

## Component and observation boundary

`MshrObserved.sv` connects the actual RTL components and exports every functional
output of this boundary, including raw cache bundles, both MSHRs' phase/address/
data/valid outputs, memory request/address/write data, allocated read ID, and
instruction-cache acknowledgement/result. The baseline has 631 input bits,
545 defined output bits, 343 flip-flop bits, and 42 word-level equality cells after
flattening and memory expansion. These are structural counts, not mapped area.

The read-ID free list uses the same return/pop handshake as
`Axi4Memory.sv:170–195`: an accepted read consumes the head ID, and a valid read
response returns its ID. The native full/empty behavior remains. Instruction
fetches are included because they share this allocator and receive response
broadcasts from `MemoryAccessController.sv:61–106`. Ignoring them would make the
ID-window argument unsound. The controller's read-busy input is connected
directly to free-list empty, exactly as in the original AXI memory block. There
is no additional throttle input or gate. Cache, recovery, and write-service
inputs remain arbitrary, so the proof includes a broader range of surrounding
behavior than ordinary core execution. A common synchronous reset is explicit.

The MSHR captures a read ID at `Cache/DCache.sv:1759–1761`; its full two-bit match
at line 1773 controls response acceptance in phase
`MSHR_PHASE_MISS_READ_MEM_RECEIVE` (numeric value 14). Saved read tags are internal
state, while every functional output using them remains observed. Other state,
including uninitialized payload fields, retains the original semantics. A
two-copy equivalence check must pair common arbitrary initial flip-flop values;
reset does not initialize every payload field. There is no output reset mask.

The shared acknowledgement type contains a `wserial` member that the original
controller never assigns for the I-cache. `ICache.sv:425–428` consumes only `ack`
and `serial`; the wrapper exports exactly those three defined bits. The omitted
bit is an unused, undefined field, not a valid-dependent output mask.
`audit_boundary.py` checks the pinned composition and consumer sources, final
port/state counts, and the precise historical wrapper changes; its evidence is
in `results/boundary_audit_v1/`.

## External contract and the ODC

The positive contract uses minimum accepted-read spacing **3 cycles**, maximum
response latency **5 cycles**, and responses in accepted-read order. Acceptance
at edge `t` allows a response at `t+1` through `t+5`; successive acceptances are
at least three edges apart. A response must name a pending accepted ID. There
are no read acceptances or responses during reset, and the initial edge is a
reset edge. Later reset pulses remain allowed. The same contract covers data
and instruction reads and every allocated ID.

`ReadServiceContract.sv` is a formal-only history monitor. It records accepted
IDs, ages, and responses. It assumes only the stated external transaction
behavior. It does **not** assume a maximum outstanding count, allocator contents,
tag matches, MSHR ownership, or any proposed comparator rewrite. The defaults in
the reusable module are 2/3; this experiment explicitly instantiates **3/5**.
The monitor and proof-only history counters are excluded from physical hardware
mapping.

Let `C` mean that an MSHR waits for a read response and a response is valid. Let
`lo` and `hi` compare the low and high bits of that MSHR's tag with the response
ID. The proved property is

```text
C && lo  ->  hi
```

Thus the original acceptance condition `C && lo && hi` can use `C && lo`. The
high comparison is not constant: separate traces reach `C && !hi` for each
MSHR. In those states `lo` is false, so the high comparison's value cannot
affect response acceptance. This is an observability don't-care, not a claim
that a saved tag bit or the high comparison is always zero/one.

The explanatory induction proves that the service bound leaves at most two
pending reads; ordered return preserves the original free-list permutation;
pending IDs are consecutive modulo four; and each waiting MSHR owns a pending
ID. Two consecutive IDs, including wraparound 3→0, have distinct low bits. These
are asserted and proved properties, never environment assumptions. The generic
automatic rewrite is checked independently against the original complete
component.

## Completed local evidence

The [compact local record](evidence/local/summary.json), copied from
`results/local_evidence_v2.json`, binds the final source, baseline JSON/Verilog,
proof files, and traces by SHA-256. `collect_evidence.py` regenerates this audit
from complete local run files without invoking synthesis or a solver. The
[local manifest](evidence/local/manifest.json) lists the committed proof logs,
four cover traces, source bindings, boundary audit, and independent review.

| Run | Contract | Result |
| --- | --- | --- |
| `results/proof_v6` | spacing 3, latency 5, ordered | Final native boundary: 18 assertions; base steps 0–7 and temporal induction pass |
| `results/proof_v6/cover_*.vcd` | identical positive model | Both MSHRs wait with two pending reads at step 6; each raw high match is false on a valid response at step 8; ID allocation wraps 3→0 at steps 10→13 |
| `results/negative_deadline_v1` | spacing 3, latency 9, ordered | Historical extra-throttle boundary: target failure at step 8; response ID 0 aliases waiting tag 2 |
| `results/negative_order_v1` | spacing 3, latency 5, unordered | Historical extra-throttle boundary: target failure at step 14 after response reordering permutes returned IDs |

The historical negative runs contain only the two target assertions, so their failures
cannot be mistaken for a failed explanatory lemma. Their raw VCDs and extracted
transaction histories are retained. Final native-boundary negative controls
must compare the actual automatically optimized component with the reference;
the historical traces alone do not establish that stronger result.

The original `proof_v4/cover.log` records all four successful covers, but its
single `cover.vcd` path retained only the last trace. The exact same SMT model
was queried again in `cover_traces/`, which retains four numbered VCD files and
a separate model-hash/command record. The original files are unchanged.

`proof_v6/invariant_bindings.json` records how source-level saved tags and free-
list nets map into the original baseline JSON. Owner 0's saved tag is
`handler.mshr[249:248]` (bits 946/947); owner 1's is `[85:84]` (1126/1127).
The original tag equality cells are `$116` and `$326`. This mapping is an audit
aid; the generic optimizer does not need handwritten tag-cell names or imported
allocator invariants to enumerate equality-width candidates.

Earlier `baseline_v1/v2` and `proof_v1/v2/v3` directories are failed development
attempts, not accepted proof results. In particular, `proof_v2` had incorrectly
elaborated internal nondeterministic inputs and failed nonvacuity coverage;
`proof_v3` failed induction. Only the positive result and covers above support
the mechanism claim. `proof_v4/v5` also passed their historical wrapper models;
the current native-composition result is `proof_v6`.

## Reproduce into fresh output directories

Run from the Pscorr repository root. Use the installed OSS CAD Suite containing
Yosys `0.70+329` (`b8d84f823`) and the Slang plugin. The source checkout must be at
the pinned RSD revision; `prepare.py` also checks each source byte against the
commit. Neither command overwrites an existing output directory.

```bash
TASK=experiments/bounded_dynamic/rsd_mshr
RSD=/absolute/path/to/rsd
TOOLBIN=/absolute/path/to/oss-cad-suite/bin
FRESH=/absolute/path/to/new-rsd-mshr-run

python3 "$TASK/prepare.py" "$FRESH/baseline" \
  --rsd "$RSD" --yosys "$TOOLBIN/yosys"

python3 "$TASK/prove.py" "$FRESH/baseline" "$FRESH/positive" \
  --toolbin "$TOOLBIN" --spacing 3 --latency 5 --depth 8 --cover-depth 20

python3 "$TASK/prove.py" "$FRESH/baseline" "$FRESH/negative-deadline" \
  --toolbin "$TOOLBIN" --spacing 3 --latency 9 --negative --depth 16

python3 "$TASK/prove.py" "$FRESH/baseline" "$FRESH/negative-order" \
  --toolbin "$TOOLBIN" --spacing 3 --latency 5 --unordered --negative --depth 28

python3 "$TASK/collect_evidence.py" /absolute/path/to/new-local-evidence.json

python3 "$TASK/audit_boundary.py" --rsd "$RSD" \
  --output /absolute/path/to/new-boundary-audit
```

The last two commands audit the complete local result paths listed above; they do not
select the fresh runs. New proof runs preserve their own monitor copy, hashes,
commands, solver logs, and numbered cover traces. The final `proof_v6` record
uses those runner conveniences. Compact committed evidence is under `evidence/`;
large local solver models are omitted and can be regenerated.

`TemporalMiter.sv` and the generic implementation in `odc/temporal.py` are owned
by the automatic optimization experiment. `control/` contains the matched
inherited-Pscorr/scorr control. Their results and any native RTL area mapping
must be reported separately from this explanatory local proof. This component
result alone establishes neither whole-core equivalence, binary adherence to
the service contract, nor a whole-core area reduction.

## Automatic rewrite and hardware result

The generic flow completed on the final native boundary (`baseline_v5`,
`odc_pdr_v4`). It enumerated both unsigned equality cells connected to the
configured `response_id` cone, proposed keeping their low bits, and proved each
cumulative change against the original. A separate combined PDR check passed.
No handwritten allocator invariant was imported into these proofs. Source
selection and external timing constraints are configuration inputs; the safe
comparison widths are discovered by the tool.

The [audited record](evidence/final/summary.json) binds the exact baseline,
generated hardware, immutable miter, proof logs and physical mapping. All other
hardware cells, state-update drivers, netnames and ports are unchanged. The
proof preserves arbitrary initial payload state and symbolic undefined values;
all 545 defined functional output bits are checked, with no reset masking.
The positive run's exact proof implementation is retained in
[evidence/final/automatic/temporal_source.py](evidence/final/automatic/temporal_source.py).

| Native hardware metric | Original | Automatic rewrite |
| --- | ---: | ---: |
| SKY130 HD mapped cell area (square micrometres) | 17,513.0464 | 17,356.6464 |
| Physical flip-flop cells | 335 | 333 |
| Total mapped cells | 1,676 | 1,679 |

The area estimate decreases **0.893%** in this component. The mapping contains
neither proof monitors nor formal initialization state. This is one matched
library-mapping result, not a layout/timing result or a whole-core result.
The original 343 RTL FF bits are counted before ordinary synthesis; the
additional temporal transformation removes two physical FF cells beyond that
same synthesis flow.

[Matched inherited-scorr controls](control/README.md) also show that the original
method already optimizes its formal model: 6,481 -> 5,445 AND nodes and 368 -> 342
encoded latches. Starting with the automatic rewrite then applying the same
scorr flow gives 5,417 AND nodes and 340 encoded latches. These encoded counts
cannot be directly compared with physical area. This establishes an additional
certified native-RTL simplification, without claiming physical superiority over
an extracted native implementation of scorr's result.

Reproduce automatic discovery and native mapping after preparing a fresh
baseline with `prepare.py`:

```sh
python3 experiments/bounded_dynamic/rsd_mshr/make_miter.py \
  "$FRESH/baseline/baseline.json" "$FRESH/miter.sv"
python3 scripts/analyze_temporal_odc.py "$FRESH/baseline/baseline.json" \
  --top MshrObserved --harness "$FRESH/miter.sv" --scope response_id \
  --engine pdr --abc /absolute/path/to/abc --yosys "$TOOLBIN/yosys" \
  --timeout 120 --output "$FRESH/automatic"
python3 scripts/map_temporal_odc.py "$FRESH/automatic" \
  --yosys "$TOOLBIN/yosys" --liberty /absolute/path/to/sky130_hd_tt.lib \
  --output "$FRESH/physical"
python3 experiments/bounded_dynamic/rsd_mshr/package_review.py \
  --baseline "$FRESH/baseline" --analysis "$FRESH/automatic" \
  --physical "$FRESH/physical" --output "$FRESH/review"
```

The package audit checks the actual two-cell delta, complete proofs, immutable
hardware hashes and absence of undefined-to-zero conversion in proof export.
It deliberately excludes large solver graphs and build products; source pins,
commands, exact generated hardware, solver logs and hashes remain reviewable.

## Functional negative controls on the automatic result

The final native reference and actual combined automatic rewrite were compared
again after relaxing one service condition at a time. All 545 defined output
bits remained observed, and all 343 common initial state bits remained paired.
The optional continuing-state equality assertion was disabled for these checks,
so an internal-state difference alone could not produce a negative result.

| Relaxed condition | Explicit functional counterexample | Validation |
| --- | --- | --- |
| Ordered responses, spacing 3, deadline 9 instead of 5 | [PDR asserted output at frame 11](evidence/negative/deadline/proof/pdr.log) | [ABC `testcex -a`: correct](evidence/negative/deadline/witness/abc.log) |
| Spacing 3, deadline 5, response ordering removed | [PDR asserted output at frame 18](evidence/negative/order/proof/pdr.log) | [ABC `testcex -a`: correct](evidence/negative/order/witness/abc.log) |

The [negative manifest](evidence/negative/manifest.json) binds the exact pair,
relaxed harnesses, proof implementation snapshots, solver logs, and counterexample
files in named-text and AIGER witness formats. Each witness was exported in a
separate rerun of the same archived AIG/PDR command, after validation; the
original counterexample logs remain unchanged. A timeout or an unproved result
does not qualify as a negative control.

```sh
python3 experiments/bounded_dynamic/rsd_mshr/prove_negative.py \
  "$FRESH/automatic" "$FRESH/auto-negative-deadline" \
  --baseline "$FRESH/baseline/baseline.json" --toolbin "$TOOLBIN" \
  --abc /absolute/path/to/abc --spacing 3 --latency 9
python3 experiments/bounded_dynamic/rsd_mshr/prove_negative.py \
  "$FRESH/automatic" "$FRESH/auto-negative-order" \
  --baseline "$FRESH/baseline/baseline.json" --toolbin "$TOOLBIN" \
  --abc /absolute/path/to/abc --spacing 3 --latency 5 --unordered
python3 experiments/bounded_dynamic/rsd_mshr/capture_negative_witness.py \
  "$FRESH/auto-negative-deadline"
python3 experiments/bounded_dynamic/rsd_mshr/capture_negative_witness.py \
  "$FRESH/auto-negative-order"
```
