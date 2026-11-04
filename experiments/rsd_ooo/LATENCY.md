# Controlled backing-read latency experiment

The retained dataset has six inputs (stream-sum and stream-mix at seeds1,7,42)
on original and dependence-cut cores at read pipeline depths5,10,20: six builds,
36 executions,18 original/cut pairs. Only
`MemoryTypes.MEMORY_READ_PIPELINE_DEPTH` varies with latency setting. Every build
retains LQ/SQ16, MSHR2, the upstream cache sizes and all other core settings.

Read/write busy-count parameters remain2. This produces a minimum accepted
request gap of3 cycles, also observed in the raw traces. Earlier build manifests
called the parameter "acceptance spacing2"; that wording was incorrect. Those
original manifests are retained unchanged. Jitter remains modulo10 with xorshift
seed1987534242. Pipeline depth is neither total read latency nor MSHR lifetime.

All36 runs satisfy the monitored ISA opcode-class superset and strict executed
memory-region contract. All18 pairs match cycles, retired instruction counts,
serial output and all five traces byte-for-byte. `summarize_latency.py` checks
the exact case set, input hashes across all settings, simulator/build-source
hashes, raw completion logs, arithmetic signatures and trace integrity. Results
are finite observations, not guaranteed bounds or full-core equivalence.

Samples follow Verilator evaluation at each rising edge. Registered MSHR valid
from sample c through d-1 gives the half-open interval[c,d), duration d-c.
Request-ack and response-valid are both settled interface signals consumed on
the following edge, so their latency is the difference of sample indices.
Requests pair with responses by serial; no pending serial is reused before its
response. MSHR lifecycle and backing-response lifecycle are analyzed separately.
The harness's reported terminal cycle N corresponds to samples0 throughN;
differences use that same origin. Partial intervals are reported separately and
excluded from complete maxima. None occur in the retained36 runs.

The typed memory accessors in `build_simulations.py` observe the actual response
pipeline state. Earlier `deep_base_p5` and `deep_cut_p5` traces used an
optimized-away response alias and must not support read-latency claims. The
retained `latency_*` runs use the corrected `deep_v2_*` binaries.

Run this recipe from the workspace root with fresh output/build names. It
requires the existing RISC-V toolchain; `bootstrap_rsd.sh` records its identity.
To regenerate candidates, the formal scripts additionally require Python Z3,
Yosys on PATH, and the pinned local yosys-slang suite named in
`formal/prove_actual_lsq.py`. The simulator builds use local Verilator4.228.

```bash
set -euo pipefail
bash experiments/rsd_ooo/bootstrap_rsd.sh
bash experiments/rsd_ooo/bootstrap_verilator.sh

# Generate the same proved candidate from pinned original RTL.
python3 experiments/rsd_ooo/formal/prove_nonalias.py
python3 experiments/rsd_ooo/formal/prove_actual_lsq.py
python3 experiments/rsd_ooo/formal/make_nonalias_candidates.py

latency_result_root=experiments/rsd_ooo/results/latency_reproduction
test ! -e "$latency_result_root"
mkdir "$latency_result_root"
python3 experiments/rsd_ooo/build_workloads.py \
  --output "$latency_result_root/inputs"

for depth in 5 10 20; do
  for variant in base cut; do
    latency_build_name="latency_repro_${variant}_p${depth}"
    candidate_args=()
    if [[ "$variant" == cut ]]; then
      candidate_args=(--candidate experiments/rsd_ooo/formal/generated)
    fi
    python3 experiments/rsd_ooo/build_simulations.py --size 16 \
      --name "$latency_build_name" --read-pipeline "$depth" --deep-trace \
      "${candidate_args[@]}"
    python3 experiments/rsd_ooo/run_workloads.py \
      --simulator "experiments/rsd_ooo/results/$latency_build_name/VMain_Zynq_Wrapper" \
      --workloads "$latency_result_root/inputs" --filter stream \
      --output "$latency_result_root/latency_${variant}_p${depth}"
  done
done
python3 experiments/rsd_ooo/summarize_latency.py \
  --results-root "$latency_result_root"
```

The summarizer reads this fresh dataset and emits its JSON/CSV summaries there;
it also derives per-run resource and lifetime records from raw traces. Running
it without arguments audits the retained original dataset. The recipe selects
only the six positive streaming inputs. Pointer-chasing and alias controls
belong to the separate capacity/contract experiment.
