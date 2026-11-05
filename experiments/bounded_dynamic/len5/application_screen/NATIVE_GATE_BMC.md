# Bounded check of the native-query gate abstraction

The single requested BMC diagnostic found a **validated abstraction-only
counterexample at frame 29**. It stopped at SAT before completing the requested
128-frame horizon. ABC took 63.016 seconds of wall time within the 120-second
budget, and a separate `testcex` invocation confirmed the trace against the
exact 684-latch/13,294-AND saved abstraction. No native counterexample,
unbounded certificate, or hardware optimization is claimed.

This result means that direct PDR cannot prove this particular abstract map
safe. The witness needs refinement or concretization against its original
folded native-arithmetic query before drawing a native-execution conclusion.
No PDR, refinement, or further target search was launched by this diagnostic.

`native_gate_bmc.py` is a separate entry point; the existing ALU-abstraction
CLI in `gate_bmc.py` remains unchanged. It validates the closed native
preparation, all 269 theorem dependencies, the complete GLA result and saved
map artifacts, and the wrapper/helper source hashes. It uses the qualified
`gate_pdr.rederive_map` to reproduce the saved abstraction byte-for-byte, then
calls `gate_bmc.run_bmc` directly on that already-folded, one-output map:

```text
read_aiger abstracted.aig; bmc3 -F 128 -T 120 -v; write_status bmc.status
```

There is no refolding, additional assumption, changed initial-state model,
or hardware rewrite. The result's full 291-file dependency map passed checks
before and after the run. The original native GLA artifacts remain unchanged.
Native hardware JSON SHA256 remains
`2426b17743dfc23d806d5c544f9c6ebbc722909ed01442f0cb41403a11ad4b48`.

Twenty tests passed: twelve native wrapper/source/budget/postcheck tests and
eight existing bounded-engine qualification tests. The latter include a real
bounded-positive toy, a testcex-validated negative, and rejection of incomplete
or contradictory terminal verdicts. Bounded absence never becomes an
unbounded certificate, and no follow-up PDR is automatic.

The raw result is `build/harvard_rom_inactive_fu_native_map_bmc_v1`.
`evidence/native_gate_bmc_v1` retains the counterexample, status, complete
solver/validation logs, exact map replay, source snapshots, source dependency
maps, and existing positive/negative engine controls. The complete source GLA
map remains in `evidence/native_gate_solver_v1/query/final_map.aig.gz`.

To reproduce after restoring the frozen native GLA run and all its source
dependencies, use fresh output directories:

```sh
python experiments/bounded_dynamic/len5/application_screen/native_gate_bmc.py \
  --gla-result /path/to/harvard_rom_inactive_fu_native_gla_v1 \
  --output /tmp/len5-native-map-bmc --frames 128 --timeout 120
python experiments/bounded_dynamic/len5/application_screen/collect_native_bmc.py \
  --run /tmp/len5-native-map-bmc \
  --toys /path/to/gate_bmc_smoke_v2 \
  --output /tmp/len5-native-map-bmc-evidence
```
