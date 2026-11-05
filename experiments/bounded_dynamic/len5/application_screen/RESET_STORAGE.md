# Conditional native reservation-station reset storage

All eight native LEN5 ALU reservation-station rows satisfy the local theorem:
after native initial reset, if `rst_ni -> !(insert && new_idx == row)` holds,
every selected payload/state bit remains equal to its original reset value.
This is a **conditional component theorem**, not a proved whole-core admission
bound, an accepted hardware optimization, or an area-saving result.

`reset_storage.py` selects the row from the original descending packed
`[DEPTH-1:0] data` and `curr_state` declarations. Numeric row zero is the
least-significant packed row; the actual native `insert` and `new_idx` aliases
bind the premise. Each selected row has 217 payload aliases and three state
aliases, implemented by ten native `$aldff` cells: **220 raw FF-Q bits**. The
native `except_raised` FF is retained even though ordinary cleanup can remove
its constant behavior; no bit is silently omitted from this theorem.

The projection preserves each selected FF's exact D/Q/AD slice, width, clock,
reset polarity and constant reset data, plus its complete native combinational
fanin. For every row this contains 1,054 original combinational cells. The 17
actual RS input-port names are parsed from the original SV header. Their
integer signal bits, plus the native insertion/index signals, form arbitrary
input boundaries; already literal native port constants retain their original
bindings. The other 142 reachable FF-Q bits become arbitrary inputs. Aliased
boundary bits share one input driver. These cuts overapproximate the original
instance; they do not assume readiness, occupancy, allocation order, tag
uniqueness, or a reconstructed state machine.

All eight positive checks pass reset base plus induction. Removing only the
no-admission premise produces a counterexample for each row at frame 2:
after reset, the component accepts that numeric row and its payload/state
becomes nonzero. These are traces of the cut-boundary component, not traces of
the actual whole-core allocator. The final premise permits arbitrary admission
during reset, matching the reset-qualified whole-core admission query. A unit
test both proves reset storage and reaches a cover with admission asserted
while reset is held, ruling out an accidentally empty reset-time domain.

The generic rewrite generator uses only the source-derived reset constants. It
deletes fully selected FF cells, or slices every width-dependent port and reset
parameter of a partially selected FF, then replaces the selected Q bits in all
remaining input edges, top-level outputs, and native aliases. Widths of native
capacity aliases and source configuration parameters remain unchanged. The
actual run generates a per-row `conditional_patch.json`; it emits no full-core
candidate or mapping. A future unbounded admission certificate must discharge
each patch's premise under the exact main environment before a rewrite can be
accepted. Current record booleans and hashes are not a standalone full-core
acceptance certificate.

The implementation rejects explicit selected-state initialization, unsupported
FF/reset/parameter shapes, dynamic or undefined reset values, input/driver
collisions, ambiguous row ordering, combinational loops, and opaque sequential
fanin. Native undefined choices are symbolized before primitive mapping and
optimization and again after sequential normalization. The final SMT model
must contain no literal undefined values. Both SMT model and lowered JSON
hashes are retained with the raw logs and negative traces.

The final run is
`/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build/reset_storage_local_v2`.
The stronger reset-time-restricted v1 is preserved at the neighboring path as
historical evidence and is not used for discharge. The compact v2 package at
[evidence/reset_storage_v2](evidence/reset_storage_v2/manifest.json) contains
95 files, 5,584,075 bytes. It includes all native projections, conditional
patches, proof logs, negative VCDs, source snapshots, license notice and hashes;
large lowered models and bulk logs remain at their recorded external paths.

From the repository root, using fresh output paths:

```sh
P=experiments/bounded_dynamic/len5/application_screen
B=/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build
Y=/home/allenjin/Projects/DAC_pscorr/tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys
python3 "$P/reset_storage.py" --source "$B/isa_baseline_prepare_v1/whole_core.json" --rs-source "$B/pre_fpu_frontend/source/rtl/expipe/exec-units/arith_rs.sv" --output "$B/reset_storage_fresh" --yosys "$Y" --timeout 20
python3 "$P/collect_reset_storage.py" --run "$B/reset_storage_fresh" --output "$P/evidence/reset_storage_fresh" --license "$B/pre_fpu_frontend/source/LICENSE"
python3 -m pytest -q tests/unit/test_reset_storage.py
```

Validation: ten tests pass, covering exact partial-FF slicing, reset parameter
ordering, unknown/initialization/collision rejection, source immutability,
positive induction, the negative admission control, nonvacuous reset-time
admission, all-alias rewrite propagation, and bounded-only rejection.
