# Native-arithmetic GLA diagnostic

The single authorized 600-second, time-limited GLA diagnostic returned
**unknown**. ABC reported a timeout in frame 29 with a one-stable abstraction;
its machine-readable status was `snl_UNK 28 unknown`. It made zero concurrent
unbounded proof calls. No validated counterexample or admission certificate
was produced. Wall time was 600.994 seconds. Other diagnostics ran concurrently,
so this is a resource-budget outcome, not an isolated runtime benchmark.

| Representation | AND nodes | Latches | Inputs |
|---|---:|---:|---:|
| Prepared native-arithmetic query | 522,336 | 22,024 | 32,247 |
| Original query after constraint folding | 424,099 | 22,025 | 32,247 |
| Final derived gate abstraction | 13,294 | 684 | 1,581 |

The extra folded latch implements constraint history. All derived maps are
proof-only overapproximations; their sizes are not hardware savings or proof
certificates. The final map is retained for diagnosis. No subsequent PDR/BMC
or continuation of this map was run here.

`native_gate_solver.py` is a separate entry point that requires native
arithmetic, the exact inactive-FU query graph, certified decoder substitution,
the seven proved word domains, external ROM closure, and the closed inactive-FU
facts. It rejects extra premises or property changes, retains the original
three assertions/eight assumptions, and checks all 269 transitive proof
dependencies before and after the engine run. Native hardware export remains
unchanged. The independent preparation review is
`review/inactive_fu_native_v1`; the separate wrapper review is
`review/native_gate_solver_v1`.

The wrapper reuses the frozen, qualified `gate_solver.run_gla`: constraints
are folded before all bad outputs are ORed, followed by
`&gla -q -T 600 -v -m`. The original `gate_solver.py` CLI remains restricted to
its earlier ALU/multiplier-abstraction experiment. An explicit unbounded GLA
terminal and `snl_UNSAT` are required for proof. A SAT result must pass
`testcex` against the original folded native-arithmetic query. Stability,
frame progress, and a smaller map do not qualify. The wrapper's historical
docstring says "bounded" only for its time budget; the engine is capable of
returning an unbounded proof.

Twenty focused tests passed: ten native wrapper scope/dependency checks and
ten existing GLA qualification tests. The latter include genuine unbounded
toy proofs, assumption-removal counterexamples, arbitrary initial-state
checks, and fail-closed verdict parsing. All 269 theorem dependencies and
the wrapper/engine/prepared-validator source hashes passed the target's
post-run check.

The raw result is `build/harvard_rom_inactive_fu_native_gla_v1`.
`evidence/native_gate_solver_v1` preserves original folded graph, saved and
final maps, derived abstraction, exact commands/tool hashes, engine logs,
strict verdict, driver snapshots, and the existing engine qualification
toys/source audit. Its `PROVENANCE.json` and `SHA256SUMS` bind every artifact.
The installed ABC binary is bound by hash; accessible local ABC source is
documented only as corroborating source, not claimed identical to that
binary.

To reproduce after restoring the source-bound preparation and its theorem
dependencies, use a fresh output directory:

```sh
python experiments/bounded_dynamic/len5/application_screen/native_gate_solver.py \
  --prepared /path/to/harvard_rom_inactive_fu_native_prepare_v1 \
  --output /tmp/len5-native-gla --timeout 600
python experiments/bounded_dynamic/len5/application_screen/collect_native_gate.py \
  --query /tmp/len5-native-gla \
  --toys /path/to/gate_solver_toys_v1 \
  --source-audit /path/to/gate_solver_source_analysis_v1 \
  --output /tmp/len5-native-gla-evidence
```

This query retains native ALU counter/address relationships. Its unresolved
result neither proves the proposed ALU admission bound nor establishes why
earlier payload-abstraction queries remained unresolved. Any future accepted
storage rewrite still requires an unbounded theorem, native implementation
validation, and the matched program-only versus program-plus-timing control.
