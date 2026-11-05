# External instruction acceptance spacing screen

The original pre-FPU LEN5 core and all capacities are unchanged. A testbench-only
gate admits an instruction request at most every two cycles. The same gate
controls memory `instr_valid_i` and core `instr_gnt_i`, so neither endpoint
accepts a request alone. An assertion and an independent VCD/CSV audit check
that equality. The response path, memory pipeline, and flush connection remain
unchanged. Cooldown resets on reset, not on flush.

The fixed core fetch FIFO remains two entries; the memory model keeps
`MemPipeNum=2`. Its original `MemEmuSkipInstrOutReg=1` bypasses the instruction
answer register, while data replies retain their register. Thus the observed
unstalled fetch latency is **two** cycles and load latency is **three** cycles.
Backpressure can lengthen fetch latency; it is not universally fixed at two.

Both final v2 runs execute the same 64-element streaming increment program and
memory image. The host checks every output address, byte enable, and value,
plus the exit store. An additional 128 zero bytes explicitly initialize RAM at
`[0x1200,0x1280)`. All previous image bytes, including instructions and the 64
input values, are unchanged. This padding matters: the retained v1 trace has a
65th speculative load at `0x1200`, returning load-access-fault code 5 after a
flush. The padded v2 traces have 65 accepted loads and **no load exceptions**;
the execution report retires 64 architectural loads. No speculative transaction
is silently excluded from the timing/fault audit.

| Platform | Reported CPU cycles | Maximum live ALU entries | Allocated ALU indices |
|---|---:|---:|---|
| Native acceptance | 805 | 6 | 1–7 |
| Minimum spacing 2 | 931 | 2 | 5–7 |

The spaced platform takes 15.65% more reported cycles; this is not software
optimization overhead. These counters are the same
upstream execution-report counters captured at program exit; raw observation
continues through the testbench's exit delay. Summaries give both the complete
trace and the interval through the accepted exit store.

The spaced trace has 489 accepted fetches, gaps 2 or 4, and 484 complete fetch
intervals of two cycles. Four requests are canceled by native flushes and one
remains pending when simulation stops. The native trace has complete fetch
intervals of 2, 3, or 7 cycles under backpressure. Both have 65 complete load
intervals, all three cycles, with no unmatched responses or live-tag reuse.

Actual dynamic issue remains visible. In the spaced run, the older ADDI at
PC `0x10` dispatches at 24 and starts ALU execution at 30. The younger independent
pointer ADDI at PC `0x18` dispatches at 28 and executes at 29. The load feeding the
older ADDI has already responded at 27; this witness establishes a younger ALU
instruction executing before an older one, not execution before that load's
memory response. There are 64 such ALU issue inversions in this finite run.

This is a finite platform/candidate screen. It does not prove an occupancy
invariant, unused slots, or safe resource removal. The use of three slots at
peak occupancy two also illustrates why peak occupancy cannot be used as a
direct queue-capacity substitution.

## Reproduction and artifacts

The new builder option is `--instruction-min-spacing 2`. Use fresh directories:

```sh
python3 experiments/bounded_dynamic/len5/qualify_simulation.py --tb-compat \
  --jobs 8 --memory-pipe-num 2 --instruction-min-spacing 2 --build /tmp/len5-gap2-build
python3 experiments/bounded_dynamic/len5/application_screen/run_streaming.py \
  --simulator-build /tmp/len5-gap2-build --output /tmp/len5-gap2-run \
  --evidence /tmp/len5-gap2-evidence
python3 experiments/bounded_dynamic/len5/application_screen/analyze_fetch_spacing.py \
  --simulator-build /tmp/len5-gap2-build --run /tmp/len5-gap2-run \
  --evidence /tmp/len5-gap2-evidence
```

Final workspace runs are `build/streaming_v2` and
`build/streaming_fetchgap2_v2` under the external LEN5 build root. The gated
simulator is `build/pre_fpu_simulation_fetchgap2_v1` (its build revision remains
v1; the padded workload runs are v2). `results/streaming*_v2` retain the full
text evidence. `evidence/fetch_spacing_v2` here contains compact unchanged raw
CSV/log/source evidence with SHA-256 manifests. Large FST/VCD files remain in
the original external run directories, with their hashes in the summaries.
