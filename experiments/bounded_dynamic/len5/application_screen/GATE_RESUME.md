# One normal-GLA continuation: inconclusive

The single authorized continuation from the saved gate map finished **unknown**
at its 600-second engine limit. It returned `snl_UNK 31 unknown` and no concrete
counterexample. ABC reports timeout while processing frame 32 at 600.16 seconds;
the measured process wall time is 600.36 seconds. There is no safety certificate,
native-core counterexample, accepted optimization, or physical saving claim.

This continuation followed the [validated frame-25 abstraction-only CEX](GATE_BMC.md).
It resumed normal `&gla`, whose internal CEGAR loop can refine the saved gate
classes and preserve a concrete result. It did not use the
[unsuitable `&gla_refine` interface](REFINEMENT_PROBE.md), and did not run PDR
alone on the unchanged abstraction. No target search followed this continuation.

Two previously qualified tiny controls established the interface before the
target run. Resuming the coarse map of the safe original refined its spurious
CEX and produced an explicit unbounded proof. Resuming the unsafe original
returned SAT with a witness that passed `testcex` against the **original folded
model**, rather than merely its abstraction. These controls used the same
`gate_resume.py` implementation as the target. Five additional unit tests check
exact state-transition preservation, retained map presence, gate-class indexing,
and rejection of hidden constraint metadata; all five pass.

The map read uses `&read -s` to disable structural hashing, with no warnings.
Before solving, the driver compares the exact ordered binary-AIG graph to the
saved original folded graph and compares the complete gate-class extension
before/after reading and writing. This binds primary-input, latch, output,
initial-state, and next-state ordering. Deriving the abstraction from the loaded
map also preserves its exact ordered graph. The actual solver invocation
exports its loaded map before starting, and that copy passes the same checks.

The continuation command is `&gla -q -T 600 -v -m ...`. There is no `-S` or `-s`
skip option, no refolding, and no new premise. The log explicitly reports
`Skip = 0`; normal GLA starts unrolling from frame zero while reusing gate
classes. `validate_prepared` and the existing transitive word/ROM dependency
checks pass before and after the target invocation.

A separate solver-free replay of the prepared source's `fold; orpos; &get`
export reproduces the original saved folded AIG **byte-for-byte**. Its expected
notice about eight AIGER constraints is checked against the input header and
the original command log. This source-import notice is distinct from the
mapping-invalidated warning rejected by the earlier interface probe; the resumed
map read has no warning. The original model and saved map are unchanged.

The continued internal refinement reached these logged checkpoints:

| Completed frame | Abstract FFs | Abstract LUTs | ABC elapsed seconds |
|---:|---:|---:|---:|
| 25 | 658 | 4,484 | 48.05 |
| 26 | 659 | 4,494 | 123.65 |
| 27 | 723 | 4,870 | 154.76 |
| 28 | 733 | 4,910 | 197.33 |
| 29 | 750 | 5,019 | 280.45 |
| 31 | 805 | 5,440 | 586.04 |

The final statistics report 237 internal counterexamples and 9,006 added objects.
Those are refinement statistics, not validated original-model violations.
Reaching a frame or changing a map does not establish the universal property.
The prior 491-FF abstraction's frame-25 CEX remains an abstraction-only result;
this continuation supplies no concrete original-model witness for it.

[Compact evidence](evidence/gate_resume_v1/PROVENANCE.json) preserves all commands,
logs/statuses, loaded/final/progress maps, map audits, source export replay,
tiny controls, implementation snapshots, and hashes: **49 files, 7,065,138 bytes**.
All package and source-dependency checks pass. The live GLA verdict helper is
byte-identical to its source-bound archived version; helper snapshots are also
included. Full raw results remain at
`/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build/harvard_rom_word_lemmas_alu_mul_gla_resume_v1`.

The original saved query already contains ALU/multiplier abstractions and
certified instruction-word lemmas. A future concrete CEX against that saved
query would still require native-RTL concretization. This result does not
resolve the main ALU admission property.

To reproduce with a fresh output directory:

```sh
BUILD=/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build
APP=experiments/bounded_dynamic/len5/application_screen
python3 -m pytest -q tests/unit/test_gate_resume.py
python3 "$APP/gate_resume.py" \
  --gla-result "$BUILD/harvard_rom_word_lemmas_alu_mul_gla_v1" \
  --output "$BUILD/gla_resume_reproduce" --timeout 600
```
