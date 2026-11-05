# Reset-cube facts in the native-arithmetic query

The combined preparation applies 42 proved reset words (583 native state bits)
to the existing decoder, instruction-domain, inactive-FU and register-status
proof query. The native hardware export and external harness remain identical.
This step ran preparation only; the three original safety obligations remain
open, and it establishes no hardware area or timing-derived storage saving.

| Native-arithmetic proof query | AIG ANDs | AIG latches | Inputs |
|---|---:|---:|---:|
| Existing RD/register-status query | 515,298 | 21,749 | 31,972 |
| Same query plus proved reset cube | 515,078 | 21,741 | 31,964 |

The net representation reduction is 220 ANDs and eight latches, including the
eight MUL/DIV CDB-arbitration state bits. The 583 source-bit substitutions and
eight removed AIG latches measure different stages and must not be equated.

The final model retains three assertions and 48 assumptions: the original
initial-reset premise, seven previously proved instruction-word domains and
40 previously proved destination-field domains. The reset cube adds no premise.
All 479 existing predicate cells, probes, 275 register-status constants and
1,761 inactive-FU constants are preserved. Native arithmetic is retained.

`formal_screen.py` accepts the explicit paired options `--reset-cube-lemmas`
and `--reset-cube-reference-prepared` only with the closed register-status
chain, `--engine prepare` and `--datapath-abstraction none`. The frozen
`reset_cube_import.py` reconstructs the complete existing query, replays the
recorded local proof exports, and applies only the certified 583-bit delta.
All 2,329 transitive dependencies are checked before and after preparation.
`reset_cube_prepared.py` validates the completed preparation and preserves the
separate native and proof-only artifacts. No solver entry point was enabled.

The completed raw output is
`build/harvard_rom_register_status_cube_native_prepare_v1`; the compact package
is `evidence/reset_cube_preparation_v1` (115 files, 2,639,491 bytes). Its 114
manifest entries verify. Large native/query netlists and AIGs remain external
with their hashes recorded in the package.

| Artifact | SHA256 |
|---|---|
| Native core JSON, unchanged | `2426b17743dfc23d806d5c544f9c6ebbc722909ed01442f0cb41403a11ad4b48` |
| External harness, unchanged | `4253300319931de8db1d9c921b714b63a72b21579ca9461bfb9670cb4b330ec6` |
| Combined query JSON | `baf5dff3bab42b3eb1b8c65ab16b8c0a744e3404c3aa2c8355e7e30e9c319cfd` |
| Lowered proof JSON | `272d07341bfd35723f71e416abcaedb00ac3bd723fd272595b14f67f70f10172` |
| Proof AIG | `7c9c57f7b8e4003d145f51e7b60f605c2fe40a762cb7c1129672656e471b310c` |

To reproduce, use the complete native-arithmetic/register-status preparation
recipe in `REGISTER_STATUS_IMPORT.md`, choose a fresh output directory, and add:

```text
--reset-cube-lemmas /path/to/reset_cube_native_fixedpoint_v1
--reset-cube-reference-prepared /path/to/harvard_rom_register_status_native_prepare_v1
```

Keep `--engine prepare --datapath-abstraction none`; both prerequisites must
retain their recorded source and proof artifacts. Package the fresh result with:

```sh
python experiments/bounded_dynamic/len5/application_screen/collect_reset_cube_preparation.py \
  --prepared /path/to/fresh-combined-preparation \
  --output /tmp/len5-reset-cube-preparation-evidence
```

The independent combined review in `review/reset_cube_import_v1` reconstructs
the exact graph delta, checks the full dependency closure and native/harness
identity, and records eight passing structural/mutation tests. The older
register-status review remains tied to its archived source; its separate
source-scope note documents the subsequent CLI extension.
