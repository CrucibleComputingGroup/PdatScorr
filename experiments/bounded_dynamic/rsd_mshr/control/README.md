# Matched correspondence control

The final control uses the frozen native RSD cache/memory composition in
`results/baseline_v5` and the proved automatic candidate in `results/odc_pdr_v4`.
Both have 631 hardware input bits, 545 defined output bits, and the same original
343 FF bits before cleanup. The wrapper audit removed an extra external busy
gate and the unassigned, unused `ICache.ack.wserial` observation before freezing
this baseline. These are component results, not a full-core optimization.

The shared `ReadServiceContract.sv` uses minimum acceptance spacing 3, maximum
response latency 5, and ordered responses. Its SHA-256 is
`66854a5606df6316600af8b339732135b42241774f7306d37d7bef59e63b7783`.
The baseline JSON hash is
`a917caae3c7a139b8c892a7271e95d962a83ab0a4c82e18c5b79232123193264`;
the automatic candidate JSON hash is
`dcba38cb3319ad2f49d4414fdefff792245dc8bd7943bc154e8391d281c875bd`.

The command sequence follows `experiments/rsd_ooo/synthesis/run_backend.py`:
`strash`, optionally `scorr -c -m -F 6 -C 30000 -S 20 -v`, then
`constr -r -p; rewrite -l; balance -l`. Each matched pair starts from exactly the
same AIG. No random-state cycling is used. Undefined combinational values become
nondeterministic inputs before the first optimization and after technology
lowering, with `opt -keepdc`. `write_aiger -zinit` preserves arbitrary FF
initialization using formal initialization inputs.

| Hardware input | Correspondence | AND nodes | Encoded latches |
|---|---:|---:|---:|
| Original | Disabled | 6481 | 368 |
| Original | Enabled | 5445 | 342 |
| Automatic two-equality candidate | Disabled | 6447 | 366 |
| Automatic two-equality candidate | Enabled | 5417 | 340 |

These are **formal encoding counts**, not mapped hardware area. Monitor state,
initialization logic, and additional symbolic inputs can remain after assumptions
are removed. Neither a successful ABC command nor a lower gate count is a
standalone RTL equivalence certificate. The separate automatic pipeline proved
the candidate against the original under the shared contract and re-proved the
combined result. Only two `$eq` cells change, each from two operand bits to one;
every original hardware input and state driver is unchanged. Different formal
PI counts reflect preprocessing, not different hardware ports.

`comparison_native_v5.json` binds the four rows to the exact original/candidate
JSON hashes, the completed automatic proof report, raw logs, commands, source
snapshots, and tool identities. Final full runs are
`runs/native_v5_original_v1` and `runs/native_v5_optimized_v1`. Compact unchanged
raw text is copied to `evidence/native_v5`; `SHA256SUMS` there verifies every
copied file. AIGs and maps remain in the full workspace runs and are not included
in this compact review copy.

Run from the repository root, using fresh output directories:

```sh
python3 experiments/bounded_dynamic/rsd_mshr/control/run_scorr_control.py \
  --baseline experiments/bounded_dynamic/rsd_mshr/results/baseline_v5/baseline.json \
  --output /tmp/rsd-original-control --spacing 3 --latency 5 --depth 6 --timeout 120
python3 experiments/bounded_dynamic/rsd_mshr/control/run_scorr_control.py \
  --baseline experiments/bounded_dynamic/rsd_mshr/results/odc_pdr_v4/optimized.json \
  --output /tmp/rsd-candidate-control --spacing 3 --latency 5 --depth 6 --timeout 120
python3 experiments/bounded_dynamic/rsd_mshr/control/summarize_control.py \
  --original /tmp/rsd-original-control --optimized /tmp/rsd-candidate-control \
  --proof-report experiments/bounded_dynamic/rsd_mshr/results/odc_pdr_v4/report.json \
  --output /tmp/rsd-control-comparison.json
```

Override `--yosys` and `--abc` when the local tool paths differ. The runner records
tool binary hashes, version output, exact commands, source and monitor hashes,
script/helper snapshots, Git HEAD, and raw logs. The summarizer checks the same
tool identities, runner, depth, contract, wrapper, ports, and source delta. It
also rechecks all input/log/AIG hashes and the optional completed automatic proof
binding without rerunning experiments.

Earlier `delta3_latency5*` and `defined_boundary*` runs, and `comparison.json`,
remain historical. They used earlier observation/wrapper boundaries or weaker
undefined-value preparation and must not be substituted for these final rows.
The first preparation failure is also preserved. None of those older families
is included in the compact final control evidence.
