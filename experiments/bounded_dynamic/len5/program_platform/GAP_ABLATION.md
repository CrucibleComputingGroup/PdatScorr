# Matched native Harvard fetch-spacing ablation

The original LEN5 core successfully runs the same frozen executable ROM and
data image with both external fetch-acceptance settings. With gap1, native ALU
rows **1, 2, and 3 are actually admitted before program exit**. This is a finite
counterexample to excluding those rows under gap1. Row 0 is not observed
admitted; the result does not claim all four rows 0–3 are used.

| Recorded quantity | Gap1, native acceptance | Gap2, external acceptance gate |
|---|---:|---:|
| All 64 expected output stores and exit zero | Pass | Pass |
| Upstream reported CPU cycles | 805 | 931 |
| Exit-store monitor cycle | 814 | 940 |
| Maximum live ALU rows before exit | 6 | 2 |
| ALU row indices admitted before exit | 1, 2, 3, 4, 5, 6, 7 | 5, 6, 7 |
| Minimum observed accepted-fetch gap | 1 | 2 |
| Completed load responses, full trace | 65 | 65 |
| Load response latency | All 3 cycles | All 3 cycles |
| Completed load faults | 0 | 0 |

The first native admissions to rows 3, 2, and 1 occur at monitor pre-edge
cycles **58, 72, and 86**, respectively. These are the actual `insert=1` and
`new_idx` values immediately before a rising edge, accompanied by the native
row-state update. Monitor edge counts and upstream reported CPU cycles use
different reporting intervals; they must not be subtracted interchangeably.
The compact trace retains all eight row states, insert/new-index signals,
selected tags, clock, and reset. Both runs also contain actual out-of-order
ALU issue witnesses.

The full gap1 trace includes one completed speculative instruction fault at
unmapped address `0x38`, accepted at monitor cycle 772 and returned at 774 with
the required **zero fault payload**. All three early row-admission witnesses
precede it. The gap2 trace has no completed instruction faults. This difference
is retained rather than hidden; both runs use the same unchanged alignment,
mapping, exception, and zero-payload lookup implementation. The data image
includes the same 128-byte padding beyond the 64 input words, so the observed
speculative 65th load completes without a data fault.

Accepted-request to accepted-response fetch latency is 2 cycles for 404 gap1
responses, 3 cycles for 2 responses, and 7 cycles for 111 responses. All 484
gap2 responses take 2 cycles. The native pipeline advances with response
readiness, so these intervals include response backpressure. The memory
pipeline code and depth are identical; a two-stage pipeline does not imply an
unconditional two-cycle accepted-response bound. Flush-canceled and end-pending
fetch requests are reported separately in the timing records.

All 74 compiled core source hashes, capacity parameters, FIFO depth 2, memory
pipeline parameter 2, qualification monitor, and memory-model bytes match.
The entire top-level testbench differs only by removal of the two-sided gap2
acceptance gate and its passive observer. ROM, data, and ELF files are copied
byte-for-byte from the successful gap2 run; no recompilation or program change
is involved. Existing builders, runners, RTL, and proof artifacts were not
edited. A fresh simulator was built with the existing builder's gap1 option.

These are two external platform configurations, so 805 versus 931 cycles is
not software optimization overhead. Finite absence of rows 0–3 in gap2 does
not establish an unbounded theorem. This ablation contains no rewrite,
capacity change, physical mapping, or accepted optimization result.

## Evidence and reproduction

- [Gap1 run and provenance](evidence/streaming_gap1_v1/summary.json).
- [Matched comparison and early admission witnesses](evidence/fetch_gap_ablation_v1/comparison.json).
- [Existing gap2 result](evidence/streaming_v1/summary.json), preserved unchanged.

The fresh external build and full raw waveform directories are
`/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build/harvard_gap1_platform_v1`
and `.../build/harvard_streaming_gap1_v1`. Compact evidence includes selected
native VCD, occupancy/event/store/timing CSVs, source snapshots, images, logs,
and SHA-256 manifests. The comparison auditor verifies both evidence manifests,
recomputes timing from saved native clock-edge observations, applies the same
through-exit window to both occupancy traces, and requires identical program
images and architectural stores. All these checks pass.

Use fresh output directories when reproducing:

```sh
BUILD=/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build
LEN5=experiments/bounded_dynamic/len5
python3 "$LEN5/qualify_simulation.py" \
  --build "$BUILD/harvard_gap1_reproduce" --instruction-min-spacing 1 \
  --memory-pipe-num 2 --tb-compat --harvard-rom --build-only --jobs 4
python3 "$LEN5/program_platform/run_gap1_ablation.py" \
  --simulator-build "$BUILD/harvard_gap1_reproduce" \
  --gap2-evidence "$LEN5/program_platform/evidence/streaming_v1" \
  --gap2-build "$BUILD/harvard_gap2_platform_v1" \
  --output "$BUILD/harvard_streaming_gap1_reproduce" \
  --evidence "$LEN5/program_platform/evidence/streaming_gap1_reproduce"
python3 "$LEN5/program_platform/audit_gap_ablation.py" \
  --gap1 "$LEN5/program_platform/evidence/streaming_gap1_reproduce" \
  --gap2 "$LEN5/program_platform/evidence/streaming_v1" \
  --output "$LEN5/program_platform/evidence/fetch_gap_ablation_reproduce"
```
