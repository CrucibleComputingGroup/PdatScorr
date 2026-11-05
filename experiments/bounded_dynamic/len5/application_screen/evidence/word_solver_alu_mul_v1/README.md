# Word-level solver feasibility result

The single authorized whole-core Pono run is **UNKNOWN**, terminated at the
120-second wall limit (120.275 seconds recorded). It reached MBIC3's blocking phase
at frame 3 and returned neither a proof nor a counterexample. No hardware
optimization is accepted, and no second target query was run.

The authoritative input is the already prepared `alu_mul` proof-only query:
`build/harvard_rom_word_lemmas_alu_mul_prepare_v1/screen.json`, SHA256
`aba14fbd94c57e0d65a999bc5d81faf792a52944aed33ed4e7031ab7a95f4f28`.
It contains the exact certified decoder, seven previously proved word-domain
lemmas, and the reviewed ALU/MUL payload overapproximation. The original strict
admission assertion and both readiness assertions remain. The source, imports,
ROM, native model, generated harness, and proof dependencies were checked before
and after the run; the final dependency map also includes validation artifacts.

The installed Pono advertises IC3IA but cannot run it: its build lacks MathSAT,
which that engine requires for interpolants. The installed `mbic3` engine with
Boolector works on bit-vector BTOR models and was used as the IC3 fallback. Local
help and capability logs are retained. MBIC3 witness extraction is also not
implemented in this binary, so the target run omits `--witness`. A future SAT
result from this configuration would be a report without a validated witness.

The direct Yosys `write_btor -s` export preserves **three semantic assertions** as
one combined bad condition and **eight constraints** (initial reset plus seven
proved lemmas). No new premise or reset/clock option is passed to Pono. The source
single-clock model is checked before `formalff -clk2ff`; already-symbolic undefined
values remain symbolic. The BTOR model retains word operations rather than first
expanding through an AIG: 64 additions and 35 subtractions remain word operators.
The 6.24 MB BTOR and the large JSON are retained externally with hashes and exact
export commands; compact logs and audit results are included here. This represents
a different solver input, not a hardware-area result or a promise that the SMT
solver avoids internal bit blasting.

The exporter reports 27 undriven alias ranges, comprising 1,112 bit occurrences.
`audit_export.py` checks the exact exported JSON: none appears at any functional
cell input or top-level output. They are unused aliases left by ordinary
preparation. No functional signal is concretized. All 23,306 FF state bits remain
uninitialized, and 36,948 symbolic-choice bits remain free. The only BTOR
initializer is the original `$initstate` bookkeeping flag. BTOR encodes the fresh
choices as states without next equations; the temporal regression below validates
their per-cycle semantics.

Nine small cases passed **before** the core run, in
`../word_solver_validation_v3/`: constrained nonzero initialized state, nonzero
initial-value rejection, uninitialized-state rejection, literal-X choices,
arbitrary symbolic choices, initial-only reset with later resets, reset release,
three-assert/eight-constraint preservation, and a failure confined to the third
assertion. Three positive cases returned explicit `unsat` plus successful checks
of invariant initiation, consecution, and implication of the property. Six negative
cases returned `sat`; separate tiny Pono BMC witnesses passed `btorsim -c`.

After the target timeout, `../word_solver_choices_v2/` strengthened the choice test
without rerunning the core. For `q <= d`, a validity bit gates checking `q == d`
until after the first edge. The `anyseq` variant fails with `d=1111` at frame 0
and `d=1110` at frame 1; its witness passes `btorsim`. The corresponding `anyconst`
variant proves with a checked invariant. This distinguishes fresh choices from
an arbitrarily selected but permanently constant value.

`word_solver.py` accepts a proof only for the configured unbounded MBIC3 engine's
explicit UNSAT result, expected exit status, and all three successful invariant
checks. Timeout, bounded-only UNSAT, missing checks, extra statuses, and errors
remain unknown. The focused parser/provenance tests are in
`tests/unit/test_word_solver.py`.

Early, preserved setup attempts are not accepted evidence: a manually written
probe initially violated BTOR node ordering, the first exporter attempt exposed
literal quote handling in Yosys's auxiliary output options, and the next tiny
run exposed unsupported MBIC3 witness extraction. Fresh validation v3 resolved
those setup issues before the one core query. Historical raw outputs remain in
the external build directories. The later paired choice validation adds no premise.
