# Independent reset-cube review

The frozen reset-cube proof passes independent source, semantics, and artifact review. No solver was launched and no owner source or target query was modified. `tests/unit/test_reset_cube_review.py` records 23 passing solver-free checks; source/model/script/log hashes and exact retained-state overlap are in `review.json`.

The input is the property-free, previously proved inactive-FU graph `bb52d686...`. Seven structural descent rounds reduce the simultaneous candidate set from 1,138 words through 1,127, 683, 530, 296, 108, and 42 words; the final 42-word set is unchanged by another round. These rounds are candidate elimination, not a bounded safety proof. Acceptance depends on the separate final reset-base and joint one-step induction SAT results, both explicit success with return code zero and no timeout.

All 42 selected native cells are `$aldff` words with zero asynchronous reset tied to native clock bit 2 and reset bit 3. The proof retains the exact native combinational D/flush logic and selector correlations. The induction hypothesis substitutes all selected **current** Q values simultaneously with their reset values. Every other state/memory output remains an arbitrary input, and the adapters compute selected **next** Q with native reset priority. No candidate fact is used as an independently accepted premise; the complete surviving cube is proved closed jointly. The separate base leaves all current Q values arbitrary and fixes only active reset `rst_ni=0`, which establishes each native reset value. Generic truth-table tests also cover both reset polarities, both enable polarities, reset-over-enable priority, and the distinction between current-Q and next-D observations.

Undefined connections are symbolized before primitive mapping or optimization, then checked again after preparation. All 81,700 initial symbolic-choice bits become unrestricted binary input bits with their exact original IDs; no chosen value is fixed. Independent comparisons verify that choice exposure removes only the symbolic drivers and preserves all other cells. The final models contain no state, hidden assertions/assumptions, or literal undefined values. SAT uses `-set-def-inputs`; only the base adds a reset constraint. The induction model safely simplifies to constant `cube_bad=0`; the base retains 62 combinational cells. Both final proof commands/logs are bound to the recorded models.

The exact patch deletes 42 whole FF cells and replaces 583 original Q bits at their consumers, aliases, and ports. Every other native cell function, memory/module metadata, and top input is preserved. The result hash is `6192d7a4...`; it is a query-only graph, not an accepted hardware or area result. The selected state consists of 421 DIV bits, 146 MUL bits, and 16 store-buffer speculative flags. All 583 replacements are zero.

The 583 bits overlap:

| Existing set | Intersection |
| --- | ---: |
| Native GLA map's 684 retained FF bits | 8 |
| 200 stored destination-register field bits | 0 |
| 275 newly proved register-scoreboard reset bits | 0 |
| 1,761 earlier inactive-FU reset bits | 0 |
| ALU reservation-station state | 0 |

The eight retained bits are the four MUL and four DIV CDB-arbiter `rem_valid_q` bits, at folded latch indices 15,434–15,441. Their identities are joined through the previously source-bound GLA mapping and checked native FF widths/Q positions. This does not measure how many combinational gates or how much solver time a future import removes.

All 284 cube dependencies and all 269 dependencies of the separately replayed prior native-query chain validate. The prior inactive-FU theorem still carries its original external instruction-domain and initial-reset premises. Universal binary inputs apply to the already-transformed `bb52...` graph; they do not make the original full-core equivalence unconditional. A future importer must bind that exact source and compose the prior theorem chain before applying only this 583-bit delta to the current query. It must preserve the separately added RD predicates, scoreboard constants, and probe boundary. This review emits no combined graph or target verdict.

The structural search is conservative and does not establish a maximal invariant set. The eight-bit retained-state overlap and the lack of any ALU-RS overlap should remain visible when choosing the next proof experiment.
