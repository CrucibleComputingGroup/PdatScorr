# Observed native counterexample: physical slot use versus occupancy

This is an observation-only repeat of `native_concretization_v2`: identical
native model, external input prefix, assumptions, target frame, and 120-second
limit. Only `-show` signals and output paths changed. SAT found the counterexample
again in 100.64 seconds. `trace_audit.json` checks that correspondence;
`native_cycles.csv` contains all 20 decoded cycles.

The accepted instruction fetches define this consistent partial immutable
instruction ROM. All nine accepted PCs are distinct; choices on unaccepted
cycles are not instructions fetched by the core.

| PC | Word | Instruction |
|---|---|---|
| 0x00 | 00028023 | `sb x0,0(x5)` |
| 0x04 | 00043503 | `ld x10,0(x8)` |
| 0x08 | 00150593 | `addi x11,x10,1` |
| 0x0c | 00150593 | `addi x11,x10,1` |
| 0x10 | 00150593 | `addi x11,x10,1` |
| 0x14 | 04000913 | `addi x18,x0,64` |
| 0x18 | 00848493 | `addi x9,x9,8` |
| 0x1c | 00001437 | `lui x8,1` |
| 0x20 | 00001437 | `lui x8,1` |

The three dependent ADDIs enter slots 7, 6, and 5 at AIG frames 11, 13, and 15.
Each waits for the load's ROB entry 1. The actual memory load request occurs at
frame 13, and its response at frame 16: the stipulated three-cycle service
latency is respected. The load broadcasts at frame 17, when the independent
`addi x18,x0,64` enters slot 4. At frame 18, slots 4–7 all request execution.
Thus a bound measured from the external request does not by itself bound the
earlier dispatch-to-request or operand-wait interval.

At frame 19, slots 4–7 are occupied. Slot 4 has completed and is removed that
edge, but `new_idx` still selects from the current empty vector. The new operation
therefore enters slot 3 while slot 4 is removed. The next occupied set is
{3,5,6,7}. Both current and combinational next-state occupancy remain at most
four throughout the retained prefix; **five distinct physical slots are used**.
This counterexample rejects the assertion that slots 0–3 are never admitted,
not an occupancy-at-most-four assertion.

The source behavior is in the pinned `rtl/expipe/exec-units/arith_rs.sv`:
`insert`/`remove` at lines 133–134, current-state empty detection at lines
120–127, admission at lines 160–185, removal at lines 229–230, state update at
lines 239–242, and `new_sel` at lines 351–358. `op_data_t.ready` is the most
significant bit, defined in `rtl/packages/expipe_pkg.sv:248`; the CSV decodes it
accordingly. RS state codes are 0=empty, 1=RS1 pending, 4=execution request,
5=execution wait, and 6=completed. The allocator does not reuse a same-edge pop.

This is a source-concrete counterexample in the broader alphabet/platform
language, and its instruction mapping is compatible with an immutable ROM.
It is **not** the actual streaming program: this prefix begins with a store,
accesses data address zero, and uses the formal environment's fault-free data
service for all addresses. It has not been run as a complete bare-platform
program and does not establish bare-platform address legality, a terminating
executable, or consistency of unified self-modifying instruction/data memory.
There is no area or accepted optimization claim.

To reproduce the observations after running `concretize_aig_prefix.py`:

```sh
python3 experiments/bounded_dynamic/len5/application_screen/concretize_observe.py \
  /tmp/len5-native-prefix-fresh /tmp/len5-native-observed-fresh \
  /tmp/len5-native-observed-evidence-fresh --timeout 120
```

The no-run `collect_native_concretization.py` accepts the frozen abstract build,
native build, native evidence directory, and optional `--observed` and
`--observed-evidence` paths to verify hashes and regenerate the decoded trace.
Yosys SAT's VCD puts step 1 at timestamp 0 and then labels steps 2–20 by their
step number. The collector checks this convention; AIG frame = SAT step − 1.
