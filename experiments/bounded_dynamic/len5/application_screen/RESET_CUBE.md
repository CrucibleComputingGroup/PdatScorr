# Standalone reset-constant cube prototype

The bounded native run proved **42 additional whole FF words, 583 bits**, constant at their native reset values. It emitted a separate, exactly audited query-only patch. This is proof simplification; it is not an ALU admission theorem, a timing-induced saving, a physical-area result, or an accepted hardware optimization. No admission query, existing proof helper/importer, or hardware export was modified.

The input is the already-closed, property-free inactive-FU query graph at `build/inactive_fu_lemmas_v1/query_only.json`, SHA-256 `bb52d686f974809e0bebd4e2b373414ec9a53af34cff5a6a48d1e5ab2465307b`. It precedes the seven word-domain predicates and any ALU/MUL payload abstraction. Its existing decoder/program/reset proof dependencies remain required when transferring this result to the original core. The new cube adds no word, timing, admission, readiness, or occupancy premise.

The pass initially considers only complete `$adff`, `$adffe`, `$aldff`, or `$aldffe` words with a fully known asynchronous reset value and the exact declared scalar top clock/reset and polarities. Other clocks, reset sources/polarities, unknown reset values, nonresettable words, and unsupported state types are not guessed constant. The one-step cone exposes every other state output as arbitrary, including memory reads, and retains the native combinational equations. The memory-output abstraction is proof-only; native memories are preserved in the emitted patch.

For a provisional set of candidates, their current Q values are replaced simultaneously by their reset words. Each candidate's effective next value follows its original D and enable polarity, with asynchronous reset taking priority. The structural pass keeps only words whose entire next-value mismatch simplifies to literal zero. Every dynamic or nonzero mismatch discards the complete word. It repeats with the weaker candidate set; discarded hypotheses never remain silently in the model. This conservative strategy may miss valid invariants and claims no maximality.

After a fixed point, two separate source-bound combinational SAT checks are mandatory. The reset-base check observes the source reset-visible Q with the top reset active. The joint induction check has no external reset constraint: it proves simultaneous transition closure of the entire remaining cube for arbitrary other state and top inputs. Their conjunction establishes the selected constants after initial reset; asynchronous reset events also preserve them. Only explicit success for both obligations, unchanged source/proof dependencies, and an exact graph audit permit a query-only patch.

Undefined values are symbolized before primitive mapping or optimization. Each symbolic choice is then exposed as a fresh unrestricted binary input, because Yosys's combinational SAT interface can otherwise display `$anyseq` as X in a witness. This chooses no constant value. Any additional undefined values after preparation are handled the same way before SAT. Source aliases and shared-control relationships are retained. The masked-X positive and unmasked-X negative tests exercise this distinction.

The initial prepare-only evidence was frozen separately in [evidence/reset_cube_prepare_v1](evidence/reset_cube_prepare_v1). It found 1,138 eligible words covering 21,882 bits. Under that provisional simultaneous cube, 1,127 mismatch outputs simplified to zero and 11 remained dynamic. This first cofactor alone certified nothing.

The authorized native descent was capped at 100 rounds and 600 seconds overall, with at most 120 seconds for the final proof phase. It completed seven rounds:

| Candidate words | Words retained |
| ---: | ---: |
| 1,138 | 1,127 |
| 1,127 | 683 |
| 683 | 530 |
| 530 | 296 |
| 296 | 108 |
| 108 | 42 |
| 42 | 42 |

The fixed point took 82.39 seconds. Reset base and joint SAT induction both passed; the final proof phase took 23.23 seconds and the complete run took 106.55 seconds. All 284 source/tool/prior-theorem dependencies matched before and after. The selected words comprise 19 DIV operand/pipeline/arbitration words (421 bits), seven MUL words (146 bits), and 16 store-buffer speculative flags (16 bits). All selected native reset values are zero. These are additional to the prior 1,761-bit input simplification.

The exact patch removes those 42 whole native FF cells and substitutes their proven values at every consumer and alias. It preserves all other cell functions, module/port/alias inventories and widths, native memories, and capacities. It adds no formal cells. The patch SHA-256 is `6192d7a41d51a0e11e8e4bb2b13128fc767ba7e4061cce27612ef7ee727e2323`. No patch was integrated into the main query or a physical candidate.

Sixteen meaningful RTL/SAT and orchestration tests pass. They cover mutually inductive nonzero words; dependent-word removal after an unconstrained input refutes a seed; active-high and active-low enables; native asynchronous-load primitives; reset priority; unmasked versus shared-control-masked X values; mismatched clock/reset domains and unknown reset values; arbitrary nonresettable and memory state; conservative removal of an entire 64-bit word when one bit can vary; prepare-only and iteration-cap failures; and a deliberately false structural fixed point rejected by the final real SAT check.

The compact final report is [evidence/reset_cube_fixedpoint_v1/result_summary.json](evidence/reset_cube_fixedpoint_v1/result_summary.json). It reconstructs the final source projections and complete patch, verifies the exact SAT scripts/logs, and binds the larger external models and full 28 MB execution summary by hash. The evidence directory retains the final source snapshots, selected words, patch manifest, proof scripts/logs, persistent tiny tests and negative witnesses. Large native models remain under `build/reset_cube_native_fixedpoint_v1` and are explicitly listed as omitted with hashes.

The [independent review](review/reset_cube_fixedpoint_v1/README.md) passed 23 solver-free tests and checked native reset/enable semantics, the simultaneous induction argument, symbolic choices, all descending rounds, and the exact patch. Eight selected bits occur in the retained native gate abstraction: four CDB arbitration bits in each inactive MUL/DIV unit. The selected bits overlap none of the 200 destination-field bits, 275 register-status constants, or prior 1,761 constants. These intersections establish scope, not an admission theorem.

Reproduce with fresh output directories:

```bash
python -m pytest -q tests/unit/test_reset_cube.py tests/unit/test_reset_cube_fixedpoint.py
python experiments/bounded_dynamic/len5/application_screen/reset_cube_diagnostic.py \
  --output /absolute/fresh/prepare --yosys /absolute/path/to/yosys
timeout 600s python experiments/bounded_dynamic/len5/application_screen/reset_cube_fixedpoint.py \
  --output /absolute/fresh/fixedpoint --yosys /absolute/path/to/yosys
```

`collect_reset_cube.py` packages source-bound existing outputs without running tools; `reset_cube_report.py` reconstructs and validates the final source/patch/proof bindings and writes the compact report. Any future admission-query import must replay this closed chain and preserve the original safety obligations. Evaluating that integration is separate work.
