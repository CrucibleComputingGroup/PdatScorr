# Independent global-CDB consumer closure audit

The source boundary is the original pre-FPU LEN5 commit
[`14291dcc5bef181085d001c5a29e7f4fc4cbc8e9`](https://github.com/edge-group-polito/len5/tree/14291dcc5bef181085d001c5a29e7f4fc4cbc8e9).
The original source and default capacities are unchanged. Paths below are under
that commit's `rtl/`. This audit concerns the **global** CDB output, not an
individual functional unit's result port.

## Source closure

`expipe/backend.sv:400-404,443-451,483-485` connects global
`cdb_others_valid/cdb_others_data` only to execution and commit stages. The
execution stage distributes it to the arithmetic, branch, operand-only and
load/store units. Commit distributes it to the ROB and same-cycle operand bypass.
The complete source references to `cdb_data_i` and their control paths were read:

| Consumer | Why invalid global payload is ignored |
| --- | --- |
| ALU/MUL/DIV arithmetic RS | `exec-units/arith_rs.sv:145-146` qualifies each matching tag with `cdb_valid_i`. State/write-operation selection at151-230 only chooses CDB operand saves when the matching forward flag holds. At289-313 EU forwarding has priority; when EU forwarding does not apply, the CDB-derived write is selected only by the valid-qualified flag. |
| Branch RS | `exec-units/branch_rs.sv:146-147` qualifies both forwarding matches. SAVE_RS operations at187-214 and corresponding writes at254-262 therefore require valid CDB data. |
| Operand-only RS | `exec-units/op_only_rs.sv:150-157` explicitly requires `cdb_valid_i`, no exception and matching ROB index before updating operand value/readiness. |
| Load buffer | `load-store-unit/load_buffer.sv:155` sets `save_rs1=cdb_valid_i`; at193-195 the only CDB-derived operation requires that flag. Payload update at328-329 is selected only by this operation. |
| Store buffer | Raw matching tags at `load-store-unit/store_buffer.sv:196-197` are intentionally unmasked. Their only state/write uses at231-256 require `save_rs=cdb_valid_i` from163. The payload saves at342-350 are consequently valid-qualified. |
| ROB | `commit-unit/rob.sv:94` sets `update_res=cdb_valid_i`; payload update at189-193 requires it. Same-cycle memory-clear bypass at122-125 also includes `cdb_valid_i`. |
| Commit-stage issue operand bypass | `commit-unit/commit_stage.sv:213-215,233-235` requires `cdb_valid_i` before selecting CDB value or marking either issue operand ready. Otherwise both raw operand values and readiness come from independent sources. |

There is no architectural-register-file write directly from this global bus;
the commit path carries that data. No assumption about operand readiness,
instruction restrictions, memory latency, reachability or occupancy is needed
for the source-level invalid-payload claim.

## Exact proof obligation

[consumer_closure.py](consumer_closure.py) operates on the manifest-bound original
whole-core RTLIL. It maps read-only ROMs, retains undefined values as symbolic
inputs, and derives a one-step combinational model from every native register:
Q becomes an arbitrary common prestate input; next-state includes the original
enable/hold mux and asynchronous-reset-dominant mux. Unsupported sequential
cells, multiple clock/edge interpretations and unexpected global CDB widths
are rejected. All original core output ports and every native next-state bit
are compared between two identical copies. Ordinary inputs, Q values, reset
and undefined choices are shared; the two 75-bit global CDB payloads vary
independently. Only the global CDB's consumer fanout is cut, retaining its
original producer. No output masking is added.

**The proof passed.** [results/consumer_closure_v3/summary.json](results/consumer_closure_v3/summary.json)
binds the original source, original RTLIL, generated models, script and logs.
The positive query is `cdb_valid=0 -> equal(outputs,next_state)` for arbitrary
common prestate. It compares 24,151 native next-state bits plus all 297 actual
core output bits. Ordinary simplification removes comparisons already identical;
all 4,864 remaining comparison bits are covered by 76 exhaustive, nonoverlapping
64-bit SAT partitions, each UNSAT for a difference. Register enables and reset
values are retained. The 37,251 generated undefined-value inputs remain symbolic
and common between copies. These are formal-model counts, not physical FF counts.

For tractability the invalid-bus proof replaces the single shared 128-bit
multiplier output with an arbitrary common input after ordinary identical-logic
merging. This is a documented overapproximation: every original multiplier
valuation remains possible, and the proof must hold for all extra valuations
as well. No multiplier relation is assumed, and no hardware is rewritten.
[arithmetic_abstraction.json](results/consumer_closure_v3/arithmetic_abstraction.json)
records the exact removed driver. The complete equality is the conjunction of
the proven partitions; no observation bit is dropped.

The complementary, **unabstracted** `cdb_valid=1` query finds a distinguishing
payload (SAT), checking that the model retains real CDB consumption. The proof
logs, source/model/script hashes, register-cut inventory and selected negative
witness signals are retained. This is a combinational noninterference lemma,
not a bounded-reachability argument or a bank-sharing equivalence certificate.

Reproduce from the code-repository root, using fresh default output directories
or explicit `--build` and `--evidence` paths:

```sh
python3 experiments/bounded_dynamic/len5/phase_sharing/consumer_closure.py
```

## Composition requirements and limits

1. The transformed ALU/RS/CDB producer must separately preserve global CDB valid
   every cycle and global CDB payload whenever valid. It must also preserve all
   other relevant interfaces, including issue readiness, EU execution behavior,
   recovery and CDB feedback. The consumer lemma alone does not establish this.
2. Do not simply discard an individual unit's payload when its local valid is
   zero. `cdb/cdb_arbiter.sv:55-56` prioritizes retained `rem_valid_q` over current
   request lines; the CDB data mux at `cdb/cdb.sv:84-87` has no output zeroing.
   A local protocol/arbiter proof must justify the global valid-qualified
   relation. Including the original CDB in the candidate proof is appropriate.
3. The RS payload update and flush behavior remain relevant: `arith_rs.sv:239-243`
   clears state on flush, while the payload process at249-324 can still write.
   The proposed operand/result sharing needs its own phase relation and complete
   producer observations; this audit does not license deleting dormant storage.
4. Equal external consumer state plus the global CDB relation permits induction
   on the untouched consumer state. If the candidate changes internal producer
   storage, its separately proved relation replaces equality for that producer;
   do not claim that this consumer lemma proves those changed Q bits equal.
5. No timing contract or physical saving is established here. Any successful
   sharing under unrestricted inputs is an automatic storage-representation
   optimization and a useful control; it must not be credited to bounded memory
   timing without a matched ablation demonstrating that dependence.
