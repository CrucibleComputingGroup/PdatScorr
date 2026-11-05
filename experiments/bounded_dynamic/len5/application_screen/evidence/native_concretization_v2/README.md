# Native concretization of the abstract frame-19 counterexample

The original, unabstracted LEN5 core reproduces the ALU admission violation with
the external input prefix recovered from the validated v5 abstract witness.
Yosys SAT found a model in 102.77 seconds, within the 120-second wall limit.
At SAT time 20 (AIG frame 19), `probe_insert=1` and `probe_index=3`.
This disproves the proposed unused-slot property in the instruction-alphabet
environment. It is not an optimization acceptance or a failure of the actual
streaming ROM.

`AUDIT.json` verifies that the native core JSON is exactly the original pinned
source export plus two observation aliases. The frozen v5 platform harness is
byte-identical. No ALU/MUL result abstraction, manual capacity change, internal
occupancy assumption, or witness initial-state restriction is present. Native
uninitialized state and undefined RTL choices retain their legal freedom; only
`rst_ni`, `instruction_choice`, `load_value`, and `invalid_code_nonzero` are fixed.
The 1,440 recovered external input bits were independently crosschecked against
ABC's named witness. Memory/readiness properties remain assertions, not premises.

The additional observation-only repeat is in
[`../native_concretization_observed_v1`](../native_concretization_observed_v1/README.md).
It reproduces the violation and explains why four occupied entries do not imply
four fixed physical slots suffice: an entry removed on the admission edge is
not available to the original first-free allocator until the following cycle.

Retained evidence includes the frozen runner, exact harness and query scripts,
external input CSV/JSON, native SAT log and witness, preparation log (compressed),
source/model hashes, and a no-run audit collector. The two approximately 18 MB
native models remain in the external build directory and are identified by hash;
they are reconstructed by the runner. The earlier `native_concretization_v1`
startup attempt failed on a Python `Path` type error before any preparation or
solver execution. It contributes no result.

Reproduce from the code repository, with the already qualified external source
and frozen `streaming_alphabet_gap2_v5_alu_mul` artifacts available:

```sh
python3 experiments/bounded_dynamic/len5/application_screen/concretize_aig_prefix.py \
  --output /tmp/len5-native-prefix-fresh \
  --evidence /tmp/len5-native-prefix-evidence-fresh --timeout 120
```

The script's default source is the frozen external v5 build. Output and evidence
directories must be new. `SHA256SUMS` covers this package. The native core pin is
`14291dcc5bef181085d001c5a29e7f4fc4cbc8e9`; source licensing and its 75-file source
binding are retained in the adjacent `formal_screen_v5` package.
