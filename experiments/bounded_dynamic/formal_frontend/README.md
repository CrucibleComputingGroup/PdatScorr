# Symbolic undefined values in formal preparation

The previous generic SMT path could prove a false equivalence by translating a
remaining unknown bit to zero. The retained example compares `s ? 1'bx : d`
with `d` under the nonempty premise `d == 0`. Both the old base check and
induction report success; the generated SMT encodes the unknown arm as `#b0`.
The corrected flow obtains an explicit counterexample from both SMT and PDR.
This is a formal-tool regression, not a processor optimization result.

`odc.temporal.formal_prepare_command(top)` is now the common preparation
sequence. It validates an ordinary top identifier, resolves the hierarchy,
cleans redundant procedural assignments, and extracts initialization
attributes. It then symbolizes undefined process/cell data before process
optimization, lowers processes with `-norom -noopt`, symbolizes new mux
defaults, and runs normal preparation. `prove_pair` also symbolizes residual
choices after asynchronous-reset normalization. No `-init` or `-params`
concretization is used; unknown initial state remains arbitrary, and the
existing initial-state and clock checks remain in force. Unsupported residual
memories and clocks still fail closed.

Native JSON export remains structural: preserve the original JSON, lower
bitwise/dynamic mux cells as needed, and write Verilog without an optimization
pass. The formal preparation helper then preserves unknown choices before
optimization. Earlier preparation of the supplied native design remains a
separate provenance obligation.

The focused suite passed 100 tests, including eleven new undefined-value
checks. Those eleven also passed with the exact pinned OSS CAD Suite used by
the processor experiments. They cover procedural and continuous unknown
arms, explicit old false certificates, both corrected proof engines,
unobservable-unknown positives, casez wildcard semantics, JSON export,
unknown initialization, and malformed top identifiers. Exact old/new inputs,
scripts, models, logs, and counterexamples are hash-bound in
[`evidence/undef_v1/summary.json`](evidence/undef_v1/summary.json).

Historical certificates are not automatically false because an undefined
choice existed or disappeared. They require revalidation with the corrected
flow, or an independent certificate that each removed choice was irrelevant
under the declared domain. The previous LEN5 phase-sharing attempts accepted
no target rewrite; their unknown outcomes remain diagnostic evidence.

Reproduce the regression with fresh temporary output:

```sh
python -m pytest -q tests/unit/test_temporal_undef.py \
  --basetemp /tmp/pscorr-undefined-regression
```
