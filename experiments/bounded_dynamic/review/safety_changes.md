# Proof-gate review and validation

The legacy ODC checker now requires an actual two-file sequential equivalence
command, a successful process, an explicit completed proof verdict, and stable
input hashes. A status string alone, a bounded pass, timeout, unknown result,
synthetic dry run, or SAT-only miter check cannot authorize a rewrite. The old
zero-argument `dsec` path could compare the current design with its own source;
the new command explicitly names the distinct reference and candidate files.

Legacy AIG checks deliberately reject embedded constraints/properties and
arbitrary latch initialization. The legacy driver does not construct a shared
contract miter for these cases, so stripping or independently interpreting
their assumptions would be unsafe. Use the temporal miter path for a shared
environment and arbitrary but paired initial RTL state. Report JSON records the
proof method, completed flag, return code, commands, hashes, and synthetic flag.
Historical synthetic/bounded results remain uncertified when re-read; dry-run
counts therefore differ intentionally from earlier behavior.

This is a limited fail-closed repair, not a validated repair of every old Ibex
injection or synthesis route. The detailed source audit remains in
`odc_pipeline_review.txt`, including ignored source injections, duplicated
drivers, bounded mux reasoning, and independent-candidate composition hazards.

The new temporal tests exercise real small Yosys/SMT and ABC/PDR fixtures:

- Conditional equality narrowing passes under the shared contract, while the
  same mutation fails with its key premise removed.
- Original input and state drivers remain byte-for-byte unchanged in the
  elaborated design; cumulative optimization is checked against the original.
- A counterexample beyond a short base bound cannot be certified by that bound.
- Uninitialized state is coupled only initially. Continuing correspondence is
  an assertion, and a changed transition still fails. Conflicting explicit
  initial values cannot be assumed equal.
- No observation assertion, an embedded candidate assumption, modified proof
  input, failed process, timeout, missing/contradictory verdict, or unsupported
  AIG property boundary can authorize a rewrite.
- PDR preserves undefined combinational values through `setundef -anyseq`
  before ABC mapping. An observable RTL `x` versus constant zero fails; the old
  implicit zero concretization is not accepted as final proof evidence.

The focused command passed **67 tests** after the undefined-value fix, the
contradictory PDR success/"was asserted" regression, and the optional-state-helper
check. Disabling that helper retains initial-state pairing and the harness
observations; a functional transition mismatch still produces a counterexample.
Clock checks reject independent or gated clocks and opposite edges before either
solver backend runs. A single-clock async-reset fixture normalizes successfully;
residual FF/latch families and unmapped memories fail closed.

```sh
PYTHONPATH=../PdatDsl python3 -m pytest -q \
  tests/unit/test_temporal_odc.py \
  tests/regression/test_sec_fail_closed.py \
  tests/regression/test_odc_analysis.py
```

This count covers the current generic unit/regression fixtures, not processor
simulation, full Ibex equivalence, or the RSD experiment's proof result. The
supplied external contract can still be vacuous; separate satisfiability and
reachability evidence is needed for a meaningful experiment. A successful
two-design proof is distinct from physical synthesis and area measurement.
