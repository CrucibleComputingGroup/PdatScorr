# Derived native MUL/DIV reset facts for proof queries

The eight native MUL/DIV reservation-station rows remain at their source reset
values under the existing Pscorr exact-program instruction domain and initial
reset. Each row has an actual base-and-induction proof, and the native issue
logic discharges its no-admission premise. This is a **program-only fact**, with
no timing, occupancy, readiness, or tag assumption. The generated artifact is
a separate query model; it is not an accepted hardware optimization or an area
measurement.

The proof chain starts with the closed
[`program_alphabet_certificate_v3.json`](../isa_baseline/results/program_alphabet_certificate_v3.json).
Its external premises are initial `rst_ni == 0` and
`(rst_ni && instr_rvalid_i) -> instruction response word in the declared domain`.
The exact 14 program words plus zero are the declared domain; arbitrary reset
and invalid-response payloads remain allowed. The certificate proves decoder
output correspondence and native word-domain propagation. The certified
decoder has unconditional `assigned_eu_o[2] == 0`. The
[native issue-register and dispatch lemmas](EU_REGISTER_LEMMA.md) then prove
visible original register bit **91687** is zero and native MUL/DIV issue-valid
bits **67868/71113** are zero. This is the reset-masked native visible register
value, not the internal raw Q introduced later by `async2sync`.

The native insertion cells are `$5863` for MUL and `$6384` for DIV. Both are
exact one-bit ANDs of their proved-zero issue-valid and arbitrary native ready.
Consequently their actual insertion bits **67870/71115** are zero. This
discharges each local premise
`rst_ni -> !(insert && new_idx == row)`; admission during reset is unrestricted
in the local theorem. There is no need to assume readiness or an internal
arrival rate. Both banks use the unchanged native `arith_rs.sv`, with four
rows each and their original capacities.

For each row, `reset_storage.py` preserves the source FF slices, reset values,
and complete combinational update fanin. Actual RS input ports, insert/index,
and other FF-Q bits become arbitrary local inputs. The numeric row binding is
the original packed `[DEPTH-1:0]` order, with row zero in the least-significant
slice. Every row projection preserves 220 native FF bits, 625 combinational
cells, and 62 other-state bit cutpoints. All eight positive proofs pass base
and induction. Removing only local no-admission yields all eight negative
controls: an admission at frame 1 followed by a nonreset selected row at frame
2. These are component cut-boundary counterexamples, not whole-core traces
feasible under the derived zero-issue-valid facts.

The source-bound generator replays the decoder certificate and regenerates
the tiny decoder/register/dispatch proof exports. The regenerated lowered
JSONs, and register SMT model, match the archived models exactly. It verifies
the external native clock/reset bindings and hashes every local proof model
and result. No solver is rerun for these three already-proved dependencies.
Safe undefined-value symbolization surrounds primitive mapping and
normalization in the new row proofs.

The query model substitutes **1,761 proved bits**: 1,760 native row-Q bits and
the one visible EU register bit. It deletes 80 native FF cells and slices the
three-bit EU FF to its two remaining bits. All consumers and aliases receive
the corresponding native reset constants. The independent collector compares
the complete query graph against the certified decoder input graph and permits
only these exact reset-state substitutions. All other cell functions, ports,
parameters, attributes, and capacity alias widths remain intact. No formal
assumptions or monitors are added to the graph.

The generic per-row patch metadata remains conditional when read alone. The
surrounding source-bound EU/dispatch/insertion chain discharges that condition
for these two banks. It does not discharge the corresponding ALU-row premises.
No whole-core ALU-admission query or physical map was launched by this task.

## Frozen results

- [Compact evidence and graph audit](evidence/inactive_fu_lemmas_v1/manifest.json):
  97 files, 3,741,819 bytes; every package hash verified.
- [Composed result and dependency hashes](evidence/inactive_fu_lemmas_v1/summary.json).
- Full raw run:
  `/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build/inactive_fu_lemmas_v1`.
- Native input SHA-256:
  `82a76125a33790027bf6b86cb97007d048759484d6e96027abd8fa9ad5d215db`.
- Separate `query_only.json` SHA-256:
  `bb52d686f974809e0bebd4e2b373414ec9a53af34cff5a6a48d1e5ab2465307b`.

The raw directory retains both full JSONs and all SMT/trace artifacts. The
compact package omits those bulky models but lists their paths and hashes.
The native input file is byte-identical to the certified candidate export.
Copied native projections are accompanied by the LEN5 license. The
[independent review](review/inactive_fu_lemmas_v1/README.md) passed: it checked
280 dependencies and reconstructed the complete substituted graph independently
of the generator's rewrite functions. Its six focused audit tests pass.
Integration with the main environment must still establish the original
external premises.

## Reproduction

Run from the `BoundedDynamicPscorr` repository with the already recorded native
frontend, decoder certificate, and EU proof dependencies present. Use fresh
output paths. This uses the existing toolchain rather than installing one.

```sh
BUILD=/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build
YOSYS=/home/allenjin/Projects/DAC_pscorr/tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys
APP=experiments/bounded_dynamic/len5/application_screen
python3 "$APP/inactive_fu_lemmas.py" \
  --eu-run "$BUILD/eu_register_lemma_v1" \
  --certificate experiments/bounded_dynamic/len5/isa_baseline/results/program_alphabet_certificate_v3.json \
  --diagnostic "$BUILD/eu_domain_diagnostic_v1" \
  --rs-source "$BUILD/pre_fpu_frontend/source/rtl/expipe/exec-units/arith_rs.sv" \
  --output "$BUILD/inactive_fu_lemmas_reproduce" --yosys "$YOSYS"
python3 "$APP/collect_inactive_fu.py" \
  --run "$BUILD/inactive_fu_lemmas_reproduce" \
  --output "$APP/evidence/inactive_fu_lemmas_reproduce" \
  --license "$BUILD/pre_fpu_frontend/source/LICENSE"
python3 -m pytest -q tests/unit/test_inactive_fu_lemmas.py \
  tests/unit/test_eu_register_lemma.py tests/unit/test_reset_storage.py
```

The focused suite passes **21 tests**, including altered admission-gate
rejection, source/clock/reset binding checks, exact FF slicing, input-driver
protection, alias updates, changed-export rejection, and rejection of an
unrelated logic change in the emitted query graph.
