# Independent inactive-FU composition review

**Verdict: no blocker found.** The frozen query-only substitution is justified
under the existing initial-reset/program-word-domain contract. This review runs
structural, provenance, witness, and equation checks; it launches no solver query,
edits no owner source/evidence, and performs no commit.

The previously reviewed EU proof chain establishes MUL issue-valid bit 67868 and
DIV issue-valid bit 71113 as zero. The exact source gates `$5863` and `$6384` each
compute `insert = issue_valid & ready`, so insert is zero for arbitrary readiness.
This discharges every local `rst_ni -> !(insert && new_idx == row)` premise. No unit
idleness, readiness, scheduling, latency, or occupancy restriction is assumed.

All four MUL rows and four DIV rows are covered. Each row contains 217 data bits
and three state bits, bound to the original packed-array indices and original
visible `$aldff` outputs. The review independently reconstructs all selected FF
slices, confirms every retained combinational cell against the original and
certified-candidate graphs, checks that arbitrary cut inputs do not collide with
retained drivers, and confirms that cut state bits are actual other FF-Q bits.
Thus the local projections overapproximate the native row transitions.

Every positive harness has exactly initial reset plus reset-qualified no-admission
as its two premises, with one assertion over all 220 visible row bits. Every
negative harness removes only no-admission. All eight positive base and induction
proofs pass; each negative witness contains a real selected-row admission and a
subsequent nonzero row. These negatives are component counterexamples, not allowed
whole-core program traces.

Undefined values are made symbolic before mux mapping or preparation, and no
literal X/Z remains in the proof models. No FF initialization attribute is added.
Every observed bit in the lowered positive models is behind the original reset
observation mux. The proof targets the original reset-visible output, never the
arbitrary internal Q introduced by `async2sync`. Admission during reset remains
unrestricted; later reset/flush behavior remains in the native transition logic.

The review reconstructs the entire final graph **directly from the certified
decoder candidate**, without calling `conditional_rewrite` or
`substitute_visible_register_high`. It independently removes the proved row FF
bits, slices the one native EU register, and replaces only those bit identities at
all original inputs and aliases. The result exactly equals the emitted
`query_only.json`:

- **1,760** row bits plus visible EU bit **91687**, totaling **1,761** constants.
- **80** whole native FF cells removed; one three-bit EU FF sliced to two bits.
- **Zero** assumptions, assertions, symbolic cells, or other formal cells added.
- All other cell functions, ports, parameters, attributes, and alias/port widths
  preserved, apart from substitution of the proved constants at their fanout.
- No capacity parameter changes or direct cuts to arithmetic/result outputs.

All recorded source and model dependencies, packaged artifacts, omitted external
models, and row proof hashes are checked. `summary.json` binds them and records the
per-row checks and concrete negative witnesses. `audit.py` implements the read-only
reconstruction; `test_audit.py` checks fail-closed driver/reset guards and witness
parsing. `SHA256SUMS` binds this review package.

The raw local theorem summaries intentionally remain marked conditional, and the
inherited proposal metadata still says its global premise is not discharged.
The final composition record supplies that discharge through the EU and insert
proofs. An importer must validate the full chain rather than treating a standalone
local summary as unconditional. Applying the program-domain theorem to the actual
Harvard producer also requires the separately proved ROM-domain closure.

This accepts the source-bound proof-model substitution, not a hardware release,
physical-area result, or whole-core admission bound. The original hardware export
remains unchanged.
