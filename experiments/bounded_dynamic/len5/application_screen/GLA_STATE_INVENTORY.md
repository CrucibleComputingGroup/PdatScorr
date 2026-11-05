# Retained state in the saved GLA abstractions

This is a read-only inventory of three existing maps. It launches no solver and establishes no new safety theorem, native counterexample, optimization, or area result. All retained latch owners resolve. The compact source-bound record is [evidence/gla_state_inventory_v1](evidence/gla_state_inventory_v1/PROVENANCE.json).

| Native hierarchy / formal state | Original map | Resumed map | Native-arithmetic map |
| --- | ---: | ---: | ---: |
| ROB | 87 | 142 | 139 |
| Issue FIFO | 85 | 112 | 123 |
| ALU reservation station | 56 | 71 | 45 |
| Register scoreboard | 12 | 56 | 30 |
| Load/store unit | 31 | 83 | 67 |
| Issue register/control | 29 | 40 | 41 |
| Branch unit | 16 | 39 | 44 |
| IFU buffers/control | 29 | 48 | 45 |
| IFU predictor | 41 | 75 | 58 |
| PC | 6 | 6 | 6 |
| Multiplier unit | 20 | 20 | 4 |
| Divider unit | 20 | 20 | 4 |
| Other native control | 14 | 15 | 15 |
| External environment | 43 | 76 | 61 |
| Export initialization tracker | 1 | 1 | 1 |
| Folded constraint-history state | 1 | 1 | 1 |
| **Total retained FF bits** | **491** | **805** | **684** |
| Map-marked original AND objects | 9,650 | 15,909 | 13,315 |

The native map's exported abstraction contains 13,294 ANDs after map derivation; 13,315 is the number of marked objects in the original ordered graph. These are distinct quantities. The native and older models also have different certified reductions/arithmetic treatment and stopped at different depths. Their counts are not a controlled solver-speed or physical-area comparison.

The old continuation adds 314 FFs and removes none. Most additions are ROB (55), load/store (52), scoreboard (44), predictor (34), environment (33), and issue FIFO (27); ALU RS adds 15. No integer register-file state or ALU operand/result value state is retained in any of these maps. The ALU RS bits principally describe its FSMs, arbitration, and ROB dependency/destination tags. In the native map they are 24 FSM bits, 16 arbitration bits, four destination-tag bits, and one exception flag. The remaining four bits in each native MUL/DIV unit are the CDB arbitration `rem_valid_q` vector; their certified inactive row state has already disappeared.

This suggests focusing on proved instruction/dependency/control facts before adding arithmetic abstractions. In the resumed map the largest overlapping marked-AND next-state cones belong to load/store (4,942), ALU RS (4,671), issue control (4,550), branch (4,444), and ROB (4,425). The native map instead has ROB 4,095, issue control 4,034, load/store 3,776, branch 3,723, and ALU RS 3,585. These cone counts overlap, stop at state/input boundaries, and are not additive area estimates.

## Existing destination-register facts

The existing RF-domain theorem covers 40 native five-bit state fields, with destination values `{0,5,8,9,10,11,18}`. Exact field/bit ownership intersects 32 retained bits in the initial map, 58 in the resumed map, and 61 in the native map:

| Covered retained state | Initial | Resumed | Native |
| --- | ---: | ---: | ---: |
| ROB destination register fields | 7 | 23 | 26 |
| Issue FIFO instruction RD fields | 13 | 20 | 20 |
| Issue register RD | 4 | 5 | 5 |
| Commit register RD | 4 | 5 | 5 |
| IFU instruction RD | 4 | 5 | 5 |

All retained scoreboard entries are inside that destination set. Initial retains counters for x5/x10; resumed retains counters for x5/x8/x9/x10/x11/x18 and last-writer tags for x5/x9/x10/x18; native retains counters for x5/x8/x9/x10/x18. Thus the proposed 275 reset bits for the 25 unused scoreboard entries intersect **zero retained FFs**. Proving those constants can still simplify the complete source model or other combinational cones; this inventory predicts no direct removal of current retained scoreboard state.

A replayed import of the existing 40 field-domain theorems would directly constrain the identified RD fields, without assuming occupancy, readiness, or tag consistency. That is a plausible next proof simplification, not a measured benefit. Further dependency-lifetime or tag-consistency facts would require new proofs in the native context. The present inventory does not supply them.

## How the names are established

1. Re-export the frozen prepared JSON through the original Yosys AIG sequence, adding only `write_aiger -vmap`/`-ywmap` metadata options. Both resulting AIG files are byte-identical to their saved source AIGs. Only the recorded formal lowering/export sequence was replayed; no solver, new query, or hardware optimization was run.
2. Compare every source latch transition and initial value with the same index in the saved folded graph. Shared hash-consing of AND DAGs uses exact PI/state-index labels, complement edges, and elementary AND constant/idempotence rules. All 22,725 old and 22,024 native latch transitions match. Exactly one folded constraint-history latch is appended. No name-based or random-simulation correspondence is used.
3. Read gate classes from the saved maps only after their original ordered graph matches the frozen folded graph exactly. Resolve each retained latch through the export map into the prepared JSON's actual FF driver and bit position. Native driver names carry the preserved hierarchy.
4. Some aliases name a visible async-reset mux output. For these, the report records the structural owner route through a constant-arm mux to the FF. This establishes ownership only: it does **not** equate reset-masked visible outputs to internal raw Q. The native RD overlap additionally checks source packed aliases, exact original FF bit positions, and the corresponding prepared owner.
5. Revalidate the old prepared query, resumed-map artifacts, native query, and all transitive dependencies before and after collection. The report distinguishes source state from the exporter/fold history state. Source-defined controls and environment registers are not silently classified as hardware datapath.

The unfiltered `-vmap` files are about 70 MB each because they include combinational aliases. The compact package includes their exact `latch` lines, full-file SHA-256 bindings, the complete per-latch reports, export commands/logs, source snapshots, and tests. It omits large source JSON/AIG files and an unused 597 MB diagnostic JSON from an earlier failed metadata-export attempt. Full data remains under `/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build/`, specifically `gla_state_inventory_v2`, `gla_native_state_inventory_v1`, and the source directories recorded in `PROVENANCE.json`.

## Recheck without a solver

From the repository root, with the original workspace artifacts present:

```sh
python3 -m pytest -q tests/unit/test_gla_state_inventory.py
python3 experiments/bounded_dynamic/len5/application_screen/collect_gla_state_inventory.py \
  --build-root /home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build \
  --output /tmp/fresh_gla_state_inventory
```

The collector requires a fresh destination and reruns structural parsing and dependency checks only. Nine unit tests cover transition/order/polarity/init mismatches, exact trivial AND rewrites, ambiguous drivers, missing/out-of-range aliases, and the distinction between reset-masked ownership and arbitrary two-state muxes. The archived certificate is used to identify already-proved native RD fields; this diagnostic does not replay that theorem or authorize its import.
