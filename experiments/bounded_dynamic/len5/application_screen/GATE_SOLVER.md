# Gate-level abstraction diagnostic

`gate_solver.py` runs the installed ABC `&gla -q` on an already inspected
ALU/multiplier proof model. It preserves the source model and every imported
theorem dependency. The sequence is `read_aiger; fold; orpos; &get; &gla`: all
eight AIGER constraints are folded before gate abstraction sees one bad output.
The native arbitrary-initial-state choices remain encoded as ordinary inputs.

The installed binary has working threaded PDR support. Its disassembly shows
`Abs_ProverThread` calling `Pdr_ManSolve` and setting the proof flag only for the
unbounded-success return. Four frozen regression models validate the actual
installed flow: an arbitrary-initial-state invariant and an eight-assumption
temporal property prove; dropping one assumption and asserting an uninitialized
FF value produce concrete counterexamples. Each negative trace is checked by
ABC `testcex` against the original folded model before export. Six additional
parser tests reject bounded results, stable abstractions, incomplete prover
messages, errors, and timeout.

The one 120-second whole-query diagnostic returned **unknown** in frame 25 with
one stable frame. ABC's default two-stable-frame trigger never fired, so the
background PDR invocation count was zero. The final map derives a proof model
with 491 flops, 9,650 ANDs, and 1,226 inputs, compared with 22,725 latches and 530,756 ANDs in
the input. The additional inputs represent abstracted internal signals. These
are proof-model sizes; the native hardware is unchanged and no admission bound
or storage removal was certified.

Only the explicit terminal unbounded-proof message together with `snl_UNSAT`,
successful process completion, and unchanged dependencies can establish safety.
Abstraction stability, completed bounded frames, a smaller map, and artifact
export do not. The last dumped map need not be the exact earlier map solved by
the background thread; the engine verdict is bound to the original folded
query. No generated gate map is a hardware candidate.

The package at `evidence/gate_solver_v1` includes the folded query, final gate
map, derived abstraction, all toy models/proofs/counterexamples, source
excerpts, installed-binary disassembly, exact commands and hashes. Binary AIGs
are gzip-compressed with hashes of their original bytes. The accessible ABC
source commit is `18f6464ec765c2ca14ede4f7a17f09011b0a0600`; it is later than the
installed binary's build date, so exact source/binary identity is not claimed.
Installed command behavior and relevant disassembly are checked separately.

Reproduce with fresh output directories after regenerating the source-bound
prepared query and certificates:

```sh
python -m pytest -q tests/unit/test_gate_solver.py
python experiments/bounded_dynamic/len5/application_screen/gate_solver.py \
  --prepared /path/to/harvard_rom_word_lemmas_alu_mul_prepare \
  --output /tmp/len5-gla-diagnostic --timeout 120
```

The original command is also recorded verbatim in the package.
`collect_gate_solver.py` packages
existing toy/query/audit directories without invoking any solver. No additional
whole-query backend run follows automatically from an unknown GLA result.

## Explicit PDR on the saved map

The separately authorized follow-up in `gate_pdr.py` rederived the saved map and
required byte-identical output before running PDR directly on that one-output
AIG. It added no folding, assumptions, or state changes. PDR returned unknown
at its 120-second budget in frame 15, without a counterexample. All original
query and theorem dependencies were verified afterward. Evidence is in
`evidence/gate_pdr_v1`.

Four additional tests validate this direct path: a proved GLA map also proves
with explicit PDR; a false toy map gives a verified counterexample; a coarse
map of an already-proved safe toy also gives a counterexample; and an input
with remaining AIGER constraints is rejected. The third test establishes why
any counterexample must be labeled abstraction-only until concretization.

```sh
python -m pytest -q tests/unit/test_gate_pdr.py
python experiments/bounded_dynamic/len5/application_screen/gate_pdr.py \
  --gla-result /path/to/recorded-gla-run \
  --output /tmp/len5-saved-map-pdr --timeout 120
```

`&read final_map.aig` restores the refined gate-class vector for a potential
future `&gla` run. It does not restore SAT clauses or a paused search. The
installed `-S N` option still unrolls from zero and skips checks through frame
N; a conservative restart omits it and rechecks the prefix. `&gla_refine`
consumes counterexamples for gate maps, whereas `&abs_refine` and
`&abs_derive` operate on flop maps. Only command/source inspection was performed;
no additional large GLA continuation was launched.
