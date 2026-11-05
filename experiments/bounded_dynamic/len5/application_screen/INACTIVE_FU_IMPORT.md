# Closed inactive-FU facts in the admission proof model

`formal_screen.py --inactive-fu-lemmas RUN_DIRECTORY` is an explicit opt-in to
the source-bound MUL/DIV reset facts. It requires the certified exact-program
decoder, all seven native instruction-word lemmas, and the exact external ROM
producer theorem. The native `core.json` and `core.v` are exported before this
operation and remain unchanged. Only a separate proof model receives the
1,761 reset-value substitutions.

The importer replays the closed decoder certificate and the small EU-register,
dispatch, and unconditional-decoder exports. It reconstructs every selected
native row projection and the complete local theorem harness, checks the exact
base/induction commands and successful logs, and regenerates all eight row JSON
and SMT models. This export-only replay runs no solver. The exact native
insertion AND gates discharge the reset-qualified local no-admission premises;
there is no added readiness, occupancy, tag, or timing assumption.

The entire substitution graph is rebuilt from the original native source,
including every FF slice, input fanout, and alias. It must equal the recorded
query artifact. An independent full-graph comparison permits only the proved
reset substitutions. The seven word lemmas are then copied byte-for-byte into
this graph; any overlap between their bits and substituted state is rejected.
Payload abstraction follows this composition and preserves those lemma cells
and the certified instruction projection.

The importer checks 269 transitive dependencies before and after preparation:
all inactive/EU/diagnostic proof-directory files, their nested dependencies,
the generators and formal frontend, and the inherited closed certificate,
native-word and ROM proof dependencies. This set is also merged into the
existing word-import dependency record, so all existing prepared-query solver
drivers check it before and after execution. A changed nested proof invalidates
the result even if a top-level summary is unchanged.

The first preparation retained the same three safety assertions and eight
assumptions. These eight are initial reset plus the seven previously proved word
domains; the inactive-FU substitution adds none.

| Same ALU/multiplier proof abstraction | AIG ANDs | AIG latches |
|---|---:|---:|
| Before inactive-FU reset substitutions | 530,756 | 22,725 |
| After inactive-FU reset substitutions | 493,830 | 20,968 |

The native hardware JSON is byte-identical in both preparations, with SHA256
`2426b17743dfc23d806d5c544f9c6ebbc722909ed01442f0cb41403a11ad4b48`.
The reductions above are **proof-model sizes**, not physical area or an accepted
hardware optimization. They follow program-only facts, not the additional
timing constraint. No target solver was launched by this integration task.

The frozen preparation is
`build/harvard_rom_inactive_fu_alu_mul_prepare_v1`; compact scripts, replay
models, logs, dependency records, and hashes are in
`evidence/inactive_fu_preparation_v1`. The underlying theorem evidence remains
in `evidence/inactive_fu_lemmas_v1`.

## Arithmetic precision

The `alu_mul` abstraction replaces every ALU result, including the program's
counter initialization at PC `0x8`, pointer increments at `0x18`/`0x1c`, and
counter decrement at `0x20`. The retained branch at `0x24` can therefore observe
arbitrary values instead of the original loop-counter relation. Every native
trace remains included, but exact instruction ROM contents alone do not recover
these data/control correlations. This is a possible precision cost, not an
established explanation of previous unknown results.

A future preparation using existing `--datapath-abstraction none` would retain
the native arithmetic. It may also allow the now-constant inactive MUL operands
to simplify naturally. Neither that preparation nor a new MUL-only abstraction
was run here; their cost and proof effect remain unmeasured.

## Reproduction

Use the recorded source-bound frontend and theorem dependencies, and a fresh
output directory:

```sh
python experiments/bounded_dynamic/len5/application_screen/formal_screen.py \
  --disassembly experiments/bounded_dynamic/len5/results/streaming_fetchgap2_v2/program.disasm \
  --program-hex experiments/bounded_dynamic/len5/application_screen/evidence/certified_decoder_admission_v1/run/program.hex \
  --zero-fault-data \
  --decoder-certificate experiments/bounded_dynamic/len5/isa_baseline/results/program_alphabet_certificate_v3.json \
  --word-domain-lemmas \
  --rom-domain-proof experiments/bounded_dynamic/len5/application_screen/evidence/rom_domain_v2/summary.json \
  --inactive-fu-lemmas /path/to/inactive_fu_lemmas_v1 \
  --output /tmp/len5-inactive-fu-prepare --gap 2 --threshold 4 \
  --datapath-abstraction alu_mul --engine prepare --timeout 120
python -m pytest -q tests/unit/test_inactive_fu_import.py \
  tests/unit/test_rom_domain_import.py tests/unit/test_domain_lemmas.py
```

The 30 focused tests pass, including all-eight-model replay, altered native
source rejection, missing external closure rejection, overlapping-word-lemma
rejection, and transitive proof mutation detection. No commit or target solver
is performed by the import command above.
