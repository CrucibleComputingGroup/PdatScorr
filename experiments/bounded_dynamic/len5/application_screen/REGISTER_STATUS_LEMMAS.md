# Native register-status reset facts from the closed destination-field domain

All 25 unused instantiated integer register-status entries are proved to remain
zero after the existing initial reset: 150 counter bits and 125 last-writer ROB
tag bits. The proof uses the original 506-cell component, including all 341
native state bits, 30 interface input bits and 12 functional output bits. Its
only local premises are initial reset and membership of the actual issue and
commit destination indices in `{0,5,8,9,10,11,18}`. All other inputs, including
valid signals, flush, read indices and ROB tags, remain arbitrary.

The two index memberships are already-proved conclusions of
`rd_domain_symbolic_v5`: the issue index is exactly native bits 461–465 and
`state_word_2`; the commit index is bits 466–470 and both `state_word_0` and the
theorem's target output. The original theorem has 40 distinct stored 5-bit
fields and 41 assertions because the target aliases the first field. Its
external premises are initial native reset and the existing reset-qualified
valid instruction-response alphabet. No timing, occupancy, readiness or
internal-idle assumption is added.

`register_status_lemmas.py` replays the frozen decoder and cumulative RF
certifiers, reconstructs the full original destination-field projection and
its 41-assertion harness, checks base/induction commands and logs, and
regenerates byte-identical theorem JSON/SMT. It then proves 50 assertions,
one counter and one tag assertion for each unused entry. Base checking covers
four steps; temporal induction succeeds at step 3. The shared native clock,
active-low asynchronous reset, synchronous flush and original update logic
are preserved. All 1,683 source/proof dependencies pass the final check.

The original source bindings are `int_regstat.sv` lines 53–70 for counter
enables and simultaneous-issue/commit suppression, lines 77–88 for tag
reset/flush/indexed update, and lines 94–107 for each counter instance.
`updown_counter.sv` lines 36–45 contain the original asynchronous reset,
synchronous clear, and enabled increment/decrement. Backend lines 299–315
connect the status indices; the commit index also drives the RF at line 324.
The native configuration gives six counter bits and five ROB-tag bits.

Both negative controls produce actual nonreset updates, not merely proof
timeouts:

| Removed derived premise | Enabled update at step 1 | Observed failure at step 2 |
|---|---|---|
| Issue-index domain | Issue destination x22 | Counter x22:0→1 |
| Commit-index domain | Commit destination x12 | Counter x12:0→63 |

The retained domain still holds in each witness; reset is deasserted and flush
is inactive for the update. The counterexample traces are retained and parsed
independently by `collect_register_status.py`.

The generated `query_only.json` replaces exactly 275 proved native Q bits by
their own zero reset values and deletes exactly 50 corresponding FF cells.
All other native cell functions, clocks, resets, ports and aliases are preserved
except those exact constant substitutions. The native input is byte-identical
to the certified cumulative RF candidate. All 381 RD-projection cells remain
unchanged by this particular substitution. No hardware candidate, physical
mapping, area measurement or full-core admission certificate is produced.

This is a program-only proof simplification. The retained-state inventory shows
that none of these 25 entries retained a FF in the current GLA maps; therefore
the 275 constants do not directly remove retained map state. Importing all 40
already-proved destination-field domains could more directly constrain the
ROB/issue refinement: 61 retained native-map bits overlap those fields. Such
predicates must use the original visible native field nets and freshly allocated
predicate bit IDs. This local run does not emit those additional assumptions.

The successful raw run is `build/register_status_lemmas_v2` and the compact
package is `evidence/register_status_lemmas_v1`. The earlier raw v1 stopped
before any local solver because it lacked the explicit historical original-RF
path; its source and setup diagnostic remain preserved. Nine focused tests
pass, including clock/reset rejection, exact native inventory, the two real
negative transitions and an independent whole-graph substitution audit.

Reproduction uses the pinned artifacts and a fresh output directory:

```sh
python experiments/bounded_dynamic/len5/application_screen/register_status_lemmas.py \
  --certificate experiments/bounded_dynamic/len5/isa_baseline/results/program_registers_certificate_v2.json \
  --rd-domain /path/to/rd_domain_symbolic_v5 \
  --original-rf /path/to/register_baseline_prepare_v1/decoder.json \
  --prepared-rf /path/to/register_baseline_prepare_v2 \
  --pair-recheck /path/to/register_pair_symbolic_v1 \
  --lowering-proof /path/to/register_lowering_symbolic_v2 \
  --output /tmp/len5-register-status \
  --yosys /path/to/pinned/yosys
python experiments/bounded_dynamic/len5/application_screen/collect_register_status.py \
  --run /tmp/len5-register-status --output /tmp/len5-register-status-evidence
```
