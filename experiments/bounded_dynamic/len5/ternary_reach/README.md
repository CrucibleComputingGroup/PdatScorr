# Pscorr plus fixed platform timing on unchanged LEN5

This directory runs the key ablation on the fixed LEN5 core: **Pscorr with
ISA/program constraints versus Pscorr with the same constraints plus the
platform's fixed timing, at equal runtime**. Both stages are Pscorr, and the
question is the additional saving. The RTL (commit `14291dc`) and capacities are
unchanged: ROB32, IQ4, ALU RS8, load buffer 8, store buffer 16, MUL/DIV/branch
RS4, RAS8 and fetch FIFO 2.

Every row starts from the same Pscorr ISA/program design C1
([isa_baseline](../isa_baseline/README.md)). Every comparison uses the same:

- reset semantics;
- closed platform;
- observation boundary (every core output);
- SKY130 HD mapping script, liberty and Yosys executable.

The compact, hash-checked record is
[`evidence/ablation_v1`](evidence/ablation_v1/): see
[`ablation.csv`](evidence/ablation_v1/ablation.csv) and
[`ablation.json`](evidence/ablation_v1/ablation.json).

**Result.** LEN5's native timing is fetch gap 1 with data replies after 3 cycles.
At that timing, Pscorr proves 321 flip-flop bits constant that vary under some
other legal timing. Almost all of them are ALU reservation-station operand and
result bits. Substituting them removes at least **18,408.9 µm²**:

- **1.31%** of the original core;
- **3.89%** of the program-optimized core;
- with runtime unchanged at 805 cycles.

The increment is modest. A larger, occupancy-driven saving (4.51% of the original
core) appears only at fetch gap 2, where the program takes 15.65% more cycles and
LEN5's fetch contract is violated.

## Evidence classes

- **Certified.** `reach.py` runs ternary (0/1/X) forward reachability with lasso
  closure ([`tsim.c`](tsim.c)) on the closed platform model. A run is accepted only
  when its invariant closes.
  - A bit is reported constant when it has the same binary value in every cube of
    the closed ternary invariant, under every reset schedule. The invariant
    over-approximates the reachable states.
  - The certificate is relative to C1. C1 itself is certified only under its
    instruction-domain assumption ([isa_baseline/evidence/final](../isa_baseline/evidence/final)).
- **Simulation bound.** Row P only; it is not certified.
- **Finite simulation evidence.** Witnesses, RTL and gate-level co-simulation, and
  trace audits.
- **Mapped area.** Yosys/ABC cell-area estimates at the SKY130 HD typical corner.
  There is no layout, timing closure, or power analysis.

## Ablation

Each row is C1 with the flip-flops that are constant in its deployment replaced by
those constants. In that deployment it therefore produces the original core's
outputs in the same cycles, so equal runtime holds by construction.

The program cycle counts were measured on the original RTL platform:

- fetch gap 1: 805 cycles ([streaming_gap1_v1](../program_platform/evidence/streaming_gap1_v1/summary.json));
- fetch gap 2: 931 cycles ([fetch_gap_ablation_v1](../program_platform/evidence/fetch_gap_ablation_v1/comparison.json)).

| Row | Information given to Pscorr | Evidence | Constant flip-flop bits | Cell area (µm²) | Cells | Reduction vs A0 | Increment over P, µm² (% of A0; % of P) | Program cycles |
|---|---|---|---:|---:|---:|---:|---:|---|
| A0 | none (original LEN5) | mapped | — | 1,400,805.98 | 160,447 | — | — | 805 at native timing |
| C1 | ISA/program: program-word decoder + architectural RF | conditionally certified | — | 1,227,165.70 | 136,304 | 12.40% | — | as A0 |
| P | C1 + flip-flops constant under every legal timing | simulation bound | 14,934 | 473,208.84 | 53,533 | 66.22% | — | as A0 |
| **T3** | **+ fixed native timing: fetch gap 1, data latency 3** | certified + RTL co-sim | 15,255 | 454,799.94 | 52,299 | 67.53% | **18,408.91 (1.31%; 3.89%)** | **805** |
| T2 | + fixed fetch gap 1, data latency 2 | certified | 15,254 | 456,261.34 | 53,955 | 67.43% | 16,947.50 (1.21%; 3.58%) | as A0 at that timing; not measured |
| T1 | + fixed fetch gap 1, data latency 1 | certified | 15,128 | 466,331.00 | 53,035 | 66.71% | 6,877.85 (0.49%; 1.45%) | as A0 at that timing; not measured |
| G12 | + constants common to fetch gaps 1 and 2 (latency 3) | certified + RTL and gate-level co-sim | 15,194 | 457,547.57 | 53,049 | 67.34% | 15,661.27 (1.12%; 3.31%) | 805 |
| G2 | + fixed fetch gap 2, data latency 3 (outside LEN5's fetch contract) | certified + RTL and gate-level co-sim | 16,172 | 410,015.74 | 47,810 | 70.73% | 63,193.11 (4.51%; 13.35%) | 931 (+15.65%) |

The core has 24,157 flip-flop bits. Each area comes from a single deterministic
map, and no mapping-noise estimate was made. Each increment works out to 35–60 µm²
per added constant bit:

| Row | µm² per added bit |
|---|---:|
| T3 | 57 |
| T2 | 53 |
| T1 | 35 |
| G12 | 60 |
| G2 | 51 |

### Why P is the program-only stage, and why the increment is a lower bound

Program-only Pscorr is given no timing, so its constants must hold at every legal
timing. P is K1 (the T3 constants) minus every bit witnessed varying in any
legal-timing run: 2,560 runs and 2,069,391,360 cycles, described below.

A certified program-only set from the same engine would exclude every bit
witnessed varying. The native timing is itself legal, so, assuming the engine
certifies nothing outside K1, that set is a subset of P. If the mapped area is
monotone in the constant set, its area is at least P's. Each increment over P is
therefore a lower bound on the increment over a certified program-only stage.

P's design is mapped only as this reference point. Its program-only status comes
from simulation, not a certificate. A single P serves every row because:

- P is contained in every fixed-timing constant set (K1, Kd2, Kd1, K12 and K2);
- no constant value conflicts with another.

The legal runs witnessed all 321 bits of K1 − P in
`random_timing_witness_v2` alone. The later runs, with delays up to 64 cycles,
found nothing else.

## Mechanism: per-row reservation-station constants

K1 − P contains 321 bits:

- **306 ALU reservation-station bits** in rows 1, 2, 5, 6 and 7 (14, 108, 62, 62
  and 60 bits). By field: `rs2_value` 184, `rs1_value` 58, `res_value` 58,
  `rs2_rob_idx` 5, `curr_state` 1.
- **7 bits** in the station's round-robin arbiters: 6 in the issue selector and 1
  in the CDB selector.
- **8 bits** of `st_idx` in the store-to-load forwarding cache.

**How fixed timing creates them.** At a fixed timing the program's schedule is
deterministic, because its control flow does not depend on load values. Each RS row
therefore receives a fixed, periodic sequence of instructions. The trace audits
show:

- row 0 is never admitted;
- at gap 1, rows 1–7 are admitted;
- at gap 2, only rows 5–7 are admitted.

Bits on which a row's instructions always agree are constant for that row.

**Why program information alone cannot remove them.** Varying the data timing
within LEN5's legal envelope reorders admissions. Other instructions then reach
those rows, and the bits vary. Every one of the 321 bits has a concrete legal run
in which it changes, so no analysis given only the ISA/program constraints and
legal timing can remove them.

Constant bits per ALU RS row (220 bits per row):

| Set | Timing | r0 | r1 | r2 | r3 | r4 | r5 | r6 | r7 |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| P | any legal timing (bound) | 220 | 113 | 5 | 5 | 5 | 5 | 5 | 4 |
| K1 | gap 1, latency 3 | 220 | 127 | 113 | 5 | 5 | 67 | 67 | 64 |
| Kd2 | gap 1, latency 2 | 220 | 127 | 114 | 5 | 5 | 67 | 67 | 64 |
| Kd1 | gap 1, latency 1 | 220 | 127 | 113 | 5 | 5 | 67 | 5 | 4 |
| K2 | gap 2, latency 3 | 220 | 220 | 220 | 220 | 220 | 182 | 182 | 9 |

**Why the zero-runtime increment is modest.** At the native timing, the station's
occupancy still reaches rows 1–7. Timing therefore adds per-row value constants
rather than idle rows. At data latency 1, rows 6 and 7 lose their timing-only
constants, so T1 adds 194 bits instead of 321.

### Fetch gap 2: larger saving, not equal runtime, not legal

At fetch gap 2 the station never fills beyond rows 5–7, so rows 1–4 become
entirely constant. K2 − K1 contains 978 bits:

| Component | Bits |
|---|---:|
| ALU reservation station rows | 865 |
| Fetch memory-interface answer register | 48 |
| Load buffer | 28 |
| Register-status busy counters | 11 |
| Store buffer | 6 |
| ALU RS CDB selector | 5 |
| ROB | 4 |
| Branch reservation station | 4 |
| CDB arbiter | 2 |
| Fetch and issue control (5 instances, 1 bit each) | 5 |

G2's increment over P is 63,193 µm² (4.51% of A0). It has two costs:

- the program takes 931 cycles instead of 805;
- gap 2 is outside LEN5's fetch contract (see below). On this program the gap-2
  RTL run still produces the same 64 results and exit store
  ([fetch_gap_ablation_v1](../program_platform/evidence/fetch_gap_ablation_v1/comparison.json)),
  but LEN5 does not guarantee that.

G2 is a performance–area trade-off, not an equal-runtime saving. G12 (the
constants common to gaps 1 and 2) is valid at gap 1 and is gate-level checked on
both platforms.

## Legal timing on LEN5

LEN5 at `14291dc` does not tolerate arbitrary interface timing:

- **Fetch.** The commit unit flushes on a mispredicted jump or branch without
  waiting for the fetch stage to accept the redirect. A fetch refusal in that cycle
  loses the redirect.
- **Data replies.** The load and store buffers accept a tag-matched reply in
  `MEM_REQ` and `MEM_WAIT`. A reply delayed past a flush can therefore be taken by
  the slot's next occupant.

The legal envelope used for P is:

- fetch is always open, as at gap 1;
- data requests are granted at random, 25–100% per regime;
- replies are delivered in order, 1 to `max` cycles after acceptance;
- the service allows 8 outstanding requests per channel, and the core never had
  more than one load and one store outstanding.

Monitors check every cycle for lost redirects, stale replies taken and
out-of-envelope latency, and each run checks the program's store sequence. All 10
legal runs passed with zero monitor events. Every bit that varied in one legal run
also varied in another.

| Legal-envelope run | Max reply delay | Runs | Cycles | K1 bits varying |
|---|---:|---:|---:|---:|
| `random_timing_witness_v2` | 3 | 1,088 | 1,026,147,840 | 321 |
| `random_timing_witness_lat64_v1` | 64 | 1,088 | 1,026,147,840 | 321 |
| `timing_envelope_sweep_v1`: lat4, 5, 6, 8, 12, 16, 32, 64 | 4–64 | 48 each | 2,136,960 each | 321, 321, 321, 319, 321, 296, 215, 215 |

Runs outside the envelope fail, which is why it is restricted. These runs are kept
as negative controls:

| Run | Timing | Failing seeds | Failures by kind |
|---|---|---:|---|
| `random_timing_witness_v1` | random fetch gate; random reply rate (unbounded delay); up to 16 outstanding | 3 / 1,040 | stores differ from the recorded RTL run: 3 |
| `random_timing_witness_refuse1_v1` | legal data timing; fetch may refuse one cycle at a time | 14 / 24 | lost redirects: 14 runs, 126 events; store sequence: 3; stores differ: 1; store count: 1 |
| `random_timing_witness_wide_v1` | unbounded fetch refusals; delays 1–7 | 35 / 48 | lost redirects: 35 runs, 468 events; store sequence: 33; store count: 10; stores differ: 7 |

### Data latency

In LEN5's memory emulator (`tb/memory/memory_bare_emu.sv`), a data reply takes
1 + `PIPE_NUM` cycles with the data answer register skipped, and one cycle more
with it.

- **This study's platform** uses `PIPE_NUM = 2` with both answer registers skipped
  (the recorded runtime testbench
  [`tb_bare.sv`](../program_platform/evidence/rom_pipeline_audit_v1/tb_bare.sv)).
  This gives the observed three-cycle data service.
- **Upstream `tb_bare`** uses `PIPE_NUM = 0`.
- **Latencies 2 and 1** need `PIPE_NUM` 1 or 0, which also shortens instruction
  responses. T2 and T1 keep the native instruction pipeline, so they model legal
  interface timings, not an emulator setting.

`program_platform/check_platform.py` instantiates the emulator with
`SKIP_DATA_ANS_REG(0)`, but only for a ROM-lookup unit test held in reset. That
instance does not set the platform timing.

## Method

No constant is chosen by hand, and the RTL and capacities are the originals.

1. **Export.** `export_closed.py` builds the closed platform around C1:
   - an immutable instruction ROM holding the program
     ([`streaming.S`](../program_platform/streaming.S): a 64-iteration
     load/increment/store loop);
   - an exact fetch gap and the native two-stage fetch pipeline;
   - a fully pipelined, nonfaulting data service that replies after exactly *d*
     cycles with arbitrary load values;
   - reset required in the first frame and unconstrained afterwards.

   It adds only observation outputs: every one of the 24,157 core flip-flop bits,
   plus a few probes.
2. **Reach.** `reach.py` runs `tsim` with 4,096 frames and a maximum period of 2,048,
   and writes the certified constants.
3. **Substitute.** `substitute.py` rewires every consumer of a certified constant
   flip-flop to its value. The flip-flops, capacities and all other connectivity
   are unchanged; synthesis removes whatever no longer reaches an output.
   - With several constants files, it applies only the bits that have the same
     value in all of them (G12).
   - With `--simulation-bound`, it applies P and marks the output as an
     uncertified bound.
4. **Map.** `isa_baseline/map.py` maps each substituted design with the same
   script, liberty and Yosys executable as A0 and C1. `map_netlist.py` re-runs a map
   to keep the netlist whose area is reported, and checks that the area is
   identical.
5. **Check and collect.** `witness.py`, `timing_witness.py`, `cosim.py`,
   `gatesim.py` and `trace_audit.py` produce the finite evidence below.
   `collect_evidence.py` checks the links between all runs and writes
   `evidence/ablation_v1`.

## Validation

| Check | Platform | Runs / cycles | Result |
|---|---|---|---|
| Fixed-timing witnesses | gap 1 | 132 / 25,607,256 | no K1 bit varies; all 978 bits certified only at gap 2 vary |
| | gap 2 | 132 / 25,607,760 | no K2 bit varies; all 61 bits certified only at gap 1 vary |
| RTL co-simulation, `--x-assign` 0 and 1 | gap 1 | 132 / 25,607,256 each | the T3 and G12 cores match the original on every output and flip-flop bit; the G2 core (negative control) diverges in 132/132 runs |
| | gap 2 | 132 / 25,607,760 each | the G2 and G12 cores match; the T3 core (negative control) diverges in 132/132 runs |
| Gate-level co-simulation from all-zero storage, `--x-assign` 0 and 1 | gap 1 | 132 / 25,607,256 each | the G12 netlist matches the original RTL on every core output; the G2 netlist (negative control) diverges in 132/132 runs |
| | gap 2 | 132 / 25,607,760 each | the G2 and G12 netlists match on every core output |
| Netlists | — | — | the G12 and G2 netlist areas and cell counts equal the reported maps |
| Trace audits | gap 1, gap 2 | 857 and 983 frames | with one fixed cycle offset, the ternary main trajectory matches the recorded native RTL simulation in both directions: ALU RS admissions by row, fetch handshakes, flushes, stores, load requests |

**Ternary precision.** The analysis can miss constants but never invents them.
These counts bound the misses from above, for this stimulus set only:

- at gap 1, 138 of the 8,388 uncertified bits never varied in the fixed-timing
  runs;
- at gap 2, 140 of 7,471 never varied.

**Coverage gaps.**

- **T3** is RTL co-simulated, but its own netlist is not gate-level simulated.
  Gate-level coverage of the native deployment comes from G12's netlist, whose
  constants are a subset of T3's.
- **T2 and T1** are certified only. They have no co-simulation, no gate-level
  simulation, and no native RTL platform at those latencies.
- **P** is a bound and has no co-simulation.

## Provenance

`evidence/ablation_v1/script_versions/` keeps every older script version that a
recorded run used:

| Script | Older version | Used by |
|---|---|---|
| `export_closed.py` | `a85c3059147a` | gap 1 and gap 2 exports |
| `export_closed.py` | `1d895bc2ba8b` | data-latency exports |
| `substitute.py` | `827916c432b4` | `*_subst_v2` |
| `timing_witness.py` | `018332915385` | unbounded run v1 |

[`provenance_v2`](evidence/ablation_v1/runs/ternary_reach_c1_provenance_v2/provenance.json)
regenerates every output of those runs byte for byte with the committed scripts, 8
of 8 identical:

- the four `ClosedPlatform.sv` files;
- the unbounded-timing platform and testbench;
- the three substituted designs.

The committed `export_closed.py` differs from `1d895bc2ba8b` only in its docstring.
That docstring now states the emulator timing above. An intermediate draft of it,
never used by an export, misdescribed the emulator's data-latency options;
`provenance_v1` (superseded) recorded that draft. `ablation.json` lists every
superseded run with its reason.

The bundle also embeds the tools that produced it:

- the collector, as `collector_source.py`;
- the provenance checker, as `provenance_check_source.py`.

`SHA256SUMS` covers every file. Large run files stay under the build root and are
listed with size and SHA-256 in `omitted_files.tsv.gz`.

## Reproduce

Use new output directories. Each run's `summary.json` records its inputs,
parameters and hashes. Witness and co-simulation records also give each run's
seed, cycle count and reset period. From the repository root:

```sh
B=/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build
X=experiments/bounded_dynamic/len5/ternary_reach
```

Checks without hardware runs:

```sh
python3 $X/provenance_check.py --build-root $B --work <new scratch dir> --output $B/ternary_reach_c1_provenance_v3
python3 $X/collect_evidence.py --build-root $B --output <new evidence dir>
python3 -m pytest -q tests/unit/test_ternary_reach.py
```

Build the T3 row from C1:

```sh
D=$B/program_registers_v2/candidate_whole_core.json   # C1, sha256 371a91db...
ROM=experiments/bounded_dynamic/len5/program_platform/evidence/rom_pipeline_audit_v1/instruction.hex
python3 $X/export_closed.py --design $D --program-hex $ROM --gap 1 --output $B/<export>
python3 $X/reach.py --model $B/<export> --output $B/<reach>
python3 $X/substitute.py --design $D --constants $B/<reach>/constants.json --output $B/<subst>
python3 experiments/bounded_dynamic/len5/isa_baseline/map.py --design $B/<subst>/design.json --output $B/<map>
```

The other rows change one option:

- **T2, T1:** `--data-latency 2` or `--data-latency 1`.
- **G2:** `--gap 2`.
- **G12:** pass the gap-1 and gap-2 `constants.json` files together.
- **P:** `substitute.py --simulation-bound --constants
  $B/ternary_reach_c1_random_timing_witness_v2/program_only_bound.json`.

## Caveats

- **Program and platform.** There is one fixed program and one data image. The
  constants are specific to the program and platform, as C1 is.
- **Closed platform.** The data service is nonfaulting with arbitrary load values,
  the ROM is immutable, and the fetch gap is fixed. Reset is required in the first
  frame.
- **Certification.** It is relative to C1, which holds under the instruction-domain
  assumption.
- **P.** It is a finite-simulation bound. The increment over P is a lower bound only
  under the assumptions stated above: the same engine certifies nothing outside K1,
  and the mapped area is monotone in the constant set.
- **Legality.** The legal envelope is established by monitors over finite runs; it
  is not proved.
- **Area.** Each area comes from a single deterministic Yosys/ABC map. There is no
  mapping-noise estimate, layout, timing or power analysis.
- **Runtime.** Equal runtime holds by construction. Only 805 cycles (gap 1) and
  931 cycles (gap 2) were measured, on the original RTL platform.
