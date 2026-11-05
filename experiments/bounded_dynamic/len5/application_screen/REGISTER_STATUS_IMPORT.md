# RD-domain and register-status facts in the native-arithmetic query

The preparation-only composition completed with the same native hardware and
external harness. It adds the 40 previously proved native destination-field
domains and substitutes 275 proved register-status reset bits in a separate
proof model. No RF candidate, new arithmetic abstraction, target solver,
physical mapping or hardware saving is part of this step.

| Native-arithmetic proof query | AIG ANDs | AIG latches | Inputs |
|---|---:|---:|---:|
| Decoder, seven word domains, inactive-FU facts | 522,336 | 22,024 | 32,247 |
| Same query plus RD/register-status facts | 515,298 | 21,749 | 31,972 |

The reduction is 7,038 ANDs and 275 latches in the proof representation. The
three original safety obligations remain open. There are 48 assumptions:
initial reset, seven existing proved instruction-word domains and 40 existing
proved RD domains. The reset substitutions add no assumptions.

`formal_screen.py --register-status-lemmas RUN` is explicitly limited to
`--engine prepare`, native arithmetic and the closed decoder/word/ROM/inactive
chain. `register_status_import.py` reconstructs and replays the RD theorem on
the original native graph before applying its new substitutions. It also
regenerates the local 50-assertion register-status proof model without rerunning
the solver. The full 506-cell native register-status component and its input
bit bindings must be identical in the original, decoder-only and inactive-FU
graphs. The cumulative RF certificate is replayed as proof provenance; its
candidate is not imported into the query.

The original RD theorem's visible 200 field bits survive the preceding closed
rewrites. Ten of its 381 projected control cells have already changed through
the proved inactive-FU reset constants. The import transfers the theorem by
that checked pointwise/outside-state equivalence; it does not incorrectly
require those ten cells to remain literally unchanged afterward. The local
275-bit reset substitution is disjoint from the existing 1,761 constants and
from all 200 RD-field bits.

The 40 fields receive 360 new predicate cells with bit IDs allocated above every
existing cell, port and alias. They observe the original visible native field
bits, not private FF nodes introduced by sequential lowering. The prior 119
word-predicate cells are preserved byte-for-byte. The final query contains 47
derived assumptions before adding the original external reset premise.

All 1,964 transitive source/proof dependencies are checked before and after
preparation and are included in the existing word-import dependency record.
`register_status_prepared.py` validates this new 48-assumption preparation
family. The older solver entry points retain their 8-assumption guards and
reject this new family; no solver permission or acceptance is implicit.

The native hardware JSON is unchanged at SHA256
`2426b17743dfc23d806d5c544f9c6ebbc722909ed01442f0cb41403a11ad4b48`.
The external harness remains
`4253300319931de8db1d9c921b714b63a72b21579ca9461bfb9670cb4b330ec6`.
The final query SHA256 is
`03445de2fa6f79055ae6df6fbc71be625a8ec0d7f024902462f7a3da80a7f79b`.
The raw preparation is `build/harvard_rom_register_status_native_prepare_v1`;
the compact package is `evidence/register_status_preparation_v1`.

Six import tests pass, including full certificate/model replay, component
mutation, unexpected query change, RD/reset overlap and missing ROM closure.
Five preparation tests pass, covering the actual completed model, unchanged
native export, extra-assumption rejection, prohibited solver/abstraction CLI
combinations and continued rejection by the legacy solver guard.

To reproduce, use the native-arithmetic preparation recipe from
`NATIVE_ARITHMETIC_PREPARATION.md` with a fresh output directory and add:

```text
--register-status-lemmas /path/to/register_status_lemmas_v2
```

Keep `--engine prepare --datapath-abstraction none`. Package the result with:

```sh
python experiments/bounded_dynamic/len5/application_screen/collect_register_status_preparation.py \
  --prepared /path/to/fresh-register-status-preparation \
  --output /tmp/len5-register-status-preparation-evidence
```

This is a closed program-only proof simplification. It does not establish the
requested admission bound or timing-derived storage savings; those still
require the unbounded target theorem and matched attribution controls.
