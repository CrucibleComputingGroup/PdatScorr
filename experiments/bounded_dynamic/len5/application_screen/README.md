# Finite streaming and external timing screen

Both platforms run the unchanged pre-FPU LEN5 core with the same capacities,
two-entry fetch FIFO, and 64-element streaming program. `run_streaming.py`
checks all 64 output stores and the exit store. The external instruction
acceptance gate in `qualify_simulation.py --instruction-min-spacing 2` gates
both endpoints of the request handshake; it preserves native flush and
response behavior. This is a platform comparison, not software optimization
overhead or a resource reduction.

| Padded v2 workload | Native platform | Minimum fetch spacing 2 |
|---|---:|---:|
| Reported CPU cycles | 805 | 931 |
| Maximum live ALU entries | 6 | 2 |
| Allocated ALU indices | 1–7 | 5–7 |
| Complete load responses | 65 | 65 |
| Load response latency | 3 cycles | 3 cycles |
| Load exceptions | 0 | 0 |

Both traces retain actual out-of-order ALU execution. The gated platform takes
15.65% more reported cycles. Its returned fetches all take two cycles; native
backpressure produces fetch intervals of two, three, or seven cycles. Peak
occupancy two still uses three distinct slots. These finite traces establish
neither an occupancy invariant nor correctness of a hardware removal.

The v1 image left address `0x1200` uninitialized. Both v1 traces have a 65th
speculative load there, returning load-access-fault code 5 after a flush;
their correct architectural stores do not qualify an exception-free platform
assumption. Version 2 explicitly initializes 128 zero RAM bytes at
`[0x1200,0x1280)`, preserving every original byte, including all instructions.
All 65 physical loads are audited in v2 and return without exception.

[FETCH_SPACING.md](FETCH_SPACING.md) documents edge sampling, handshake and
flush semantics, witnesses, limitations, and reproduction commands.
`analyze_fetch_spacing.py` derives transactions from the native VCD interface
and cross-checks the gated monitor CSV; it does not rerun simulation.
`collect_fetch_spacing.py` copies compact evidence and verifies source hashes,
identical core files and capacities, image padding, completion, and faults.

The frozen compact packages are `evidence/fetch_spacing_v2` and
`evidence/fault_control_v1`. Each has a `SHA256SUMS` and original absolute source
paths. Regenerate into fresh directories with `collect_fetch_spacing.py
--output NEW_DIRECTORY`, adding `--workload-version 1` for the fault control.
Full waveforms remain under
`/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build/streaming*_v{1,2}`;
their hashes are retained in the timing summaries. The original text evidence
is under `../results/streaming*_v{1,2}`. These packages contain no formal proof
results and make no area claim.
