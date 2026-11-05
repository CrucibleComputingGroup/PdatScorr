# Proved native execution-unit selector facts

The native visible issue-register bit `ireg_data_out.assigned_eu[2]` is now
proved zero after native initial reset, and the exact native dispatch logic
proves both MUL and DIV issue-valid inputs zero. These are **Pscorr program-only
facts**, under the existing instruction-word domain. There is no timing premise,
new environmental restriction, accepted hardware rewrite, or area claim.

The proof chain is explicit:

1. Replay the final exact-alphabet decoder certificate v3. It establishes the
   program-word input domain and all-output decoder substitution, preserving
   outside state under initial reset and
   `(rst_ni && instr_rvalid_i) -> response word in the declared domain`.
2. Verify the existing unconditional combinational SAT result for the exact
   certified candidate decoder: output bit 202160 is zero. Its component cells
   match the certified native candidate, its harness has no assumptions, and
   its safe lowered output is literal zero.
3. Project the original visible register bit **91687**, preserving the exact
   selected D/Q/AD slice of its native `$aldff` and all three native mux slices.
   The enable and flush controls are arbitrary inputs. The inner undefined
   flush arm and outer zero override retain the same native selector. Under
   native initial reset and the already-derived decoded-high-zero fact, reset
   base plus induction proves the visible register high bit zero.
4. Preserve the original one-hot demux and valid-AND cells. Complete
   combinational SAT, with the preceding registered-high-zero conclusion,
   proves native MUL issue-valid bit **67868** and DIV issue-valid bit **71113**
   both zero. The other selector bits and issue-valid gate remain arbitrary.

The register lemma observes the original native visible Q alias, not the
arbitrary internal FF introduced by `async2sync`. This distinction preserves
initial-state semantics: reset can mask an initially arbitrary internal state.
No permanent unit-idle assumption is inserted. Each local proof premise is
discharged by the preceding theorem and the closed decoder/domain certificate.

Both negative controls fail when their derived premise is removed: the register
can become nonzero with a nonzero decoded high bit, and the native dispatch can
select MUL/DIV when the registered high bit is free. A separate unit regression
changes the inner flush selector to an independent input; the previously
masked undefined arm then produces a counterexample. This checks that the
proof depends on the actual shared selector, rather than an invented relation
or concretized undefined value. All three focused tests pass.

The lemmas support a future proof-cone simplification, but they do not alone
authorize deleting FU state or outputs. Native reset/state/output closure for
the never-admitted units is still required. No whole-core proof or physical
mapping was run in this task.

The [complete small evidence package](evidence/eu_register_lemma_v1/manifest.json)
includes the projections, safe scripts, lowered models, SMT models, positive
logs, negative VCDs, source snapshot, replayed decoder certificate, dependency
hashes and license notice. Full original artifacts remain at
`/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build/eu_register_lemma_v1`.

```sh
P=experiments/bounded_dynamic/len5/application_screen
B=/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build
python3 "$P/eu_register_lemma.py" --certificate experiments/bounded_dynamic/len5/isa_baseline/results/program_alphabet_certificate_v3.json --diagnostic "$B/eu_domain_diagnostic_v1" --output "$B/eu_register_lemma_fresh" --yosys /home/allenjin/Projects/DAC_pscorr/tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys
python3 -m pytest -q tests/unit/test_eu_register_lemma.py
```
