# Pscorr's own flow on an out-of-order core and an in-order core with a non-blocking cache

Here Pscorr means its paper flow:

1. constraints are written in CRISP;
2. the CRISP compiler generates SVA assumptions;
3. the assumptions are injected into the RTL, and Yosys exports an AIGER in which they
   are constraints;
4. ABC `scorr -c` proves sequential equivalences under the constraints, and the
   result is mapped to SKY130 HD.

No other prover is involved, and the RTL, its parameters and its capacities are
never changed. This study asks two questions:

1. **Scalability.** Does the flow, with ISA constraints only, run on a much larger
   core than the paper's Rocket? LEN5 is out of order, RV64, and about 12× Rocket's
   area.
2. **Microarchitectural constraints.** Does the same flow give additional savings
   when CRISP also states the platform's memory wait-time bounds? This is tested on
   LEN5 and on CVA6, an in-order core with a non-blocking HPDcache.

## Changes to the flow

There are two deliberate changes. The main idea stays the same.

- **CRISP generator.** It lives in PdatRiscvDsl, branch `feat/bounded-dynamic-crisp`.
  - New declarations `grant_latency <channel> N` and `response_latency <channel> N`
    bound how long a request waits to be accepted and how long an accepted request
    waits for its response.
  - The generator emits per-request monitors with assumptions; see
    [mechanism/README.md](mechanism/README.md).
  - The existing template only bounds request-acceptance stalls. It cannot express a
    response wait-time, which is what limits the occupancy of request-tracking tables.
  - Fix: the v2 ISA generator now honours `has_compressed_check`. LEN5 has no
    compressed instructions, so it must not exempt 16-bit encodings.
- **ABC script.** The stock command starts with `cycle 100`, a random, unconstrained
  100-cycle simulation whose final state becomes scorr's initial state. That makes
  results depend on the random run.
  - `--flow reset` drops `cycle 100` and assumes reset in the first cycle, leaving
    reset free afterwards.
  - On the mechanism test this gives deterministic results that equal the exact
    reachable set.
  - `--flow stock` keeps the original command, for comparison with the paper's runs.

## Frontends

- **Synlig:** used by the paper's flow, but it cannot parse LEN5 (`foreach`) or CVA6.
- **yosys-slang:** used instead, with the stock Yosys command sequence. On the
  mechanism test it gives the same scorr result as Synlig.
- **CVA6 SRAMs:** CVA6's SRAM macros are black boxes, and `expose -evert` turns their
  pins into top-level ports, so:
  - cache contents (SRAM read data) are unconstrained inputs;
  - the logic driving SRAM addresses, write data and enables stays observed.

## Results

### LEN5, ISA constraint at the fetch port: nothing reaches the decoder

The ISA assumption here sits where Rocket's does: on the instruction-memory read data
at the core's port, `instr_rdata_i`. All rows use depth 1 and reset semantics; the
bundle is [`evidence/len5_port_k1_v1`](evidence/len5_port_k1_v1/).

| CRISP | Latches after | AND gates after | scorr time (s) | Cell area (µm²) |
|---|---:|---:|---:|---:|
| no scorr (stock map of the unchanged AIG) | 23,698 | 469,953 | — | 1,996,366 |
| none | 23,683 | 387,627 | 14,887 | 1,777,211 |
| RV64IM | 23,643 | 387,244 | 15,221 | 1,771,052 |
| RV64IM + bounded interface timing | 23,643 | 387,235 | 14,554 | 1,775,165 |
| RV64IM + exact native timing | 23,643 | 387,263 | 14,800 | 1,774,353 |
| 19 Embench RV64IM subsets (21–44 of 65 instructions) | 23,643 | 387,136–387,244 | 14,214–15,081 | 1,774,249–1,776,063 |

None of these constraints changes the design beyond mapping noise. Even workloads
that forbid whole groups of instructions save nothing.

The reason is the injection site. LEN5 keeps the raw instruction word in a fetch
spill register and its 4-entry issue queue, and decodes it only at issue. To use the
port constraint, `scorr` would have to prove that the stored word lies in the allowed
set. That fact is neither a constant nor an equivalence, so `scorr` cannot express it.

Rocket and Ibex inject at (or next to) decode. The decoder-site rows below inject at
the issue decoder input, valid entries only, as for CVA6.

The 11% gap between "no scorr" and every other row comes from ABC's
`rewrite -l; balance -l` and the mapping. It is not a constraint effect.

The `sglib-combined` row was validated by AIG co-simulation: 2.05M live trace-cycles,
with no violated assumption and no output mismatch.

### LEN5, ISA constraint at the issue decoder

**First attempt (`--isa-site decoder`).** The constraint applied to valid
issue-queue entries without a fetch exception. It still removed almost nothing: the
streaming kernel's 8 operations, with no multiply or divide, gave 1,771,060 µm²,
23,683 latches and 386,475 AND gates.

The issue register loads on every valid entry (`ireg_en = iq_cu_valid &
cu_iq_ready`), including entries with a fetch exception, and dispatch reads
`ex_valid[ireg.assigned_eu]`. An exception-flagged entry with an arbitrary word can
therefore leave a multiply-unit code in the register. Ruling that out needs an
implication between the control state and the register's contents, which `scorr`
cannot express.

**Second attempt (`--isa-site decoder-valid`).** The constraint applies to every valid
entry. That is no stronger than the port constraint, which applies to every word.
Every value the issue register latches is then a constrained decode, and plain
induction can show that it never selects an unused unit.

A vacuity check found no violation of the decoder-site assumption: with legal words
at the port, it holds on every trace over 1.02M live trace-cycles.

### CVA6: in-order core with a non-blocking HPDcache

The design is CVA6 d33a4fb9, stock cv32a60x, with no configuration edits:

- RV32 with B, C and Zcb, no FPU and no MMU;
- 2-way 2 KB I$ and D$;
- HPDcache with a 2-way MSHR, a 4-entry replay table and an 8-entry write buffer.

Each outstanding request has its own AXI ID, and responses may come back out of
order. The flow uses reset semantics, and every run uses the same frontend, the same
black-boxed SRAMs and the same mapping.

The timing rows add `grant_latency 0` on AR, AW and W, and per-ID
`response_latency N` on reads (last R beat) and writes (B).

| CRISP | Depth | Latches | AND gates | scorr time (s) | Cell area (µm²) | vs unconstrained | vs RV32IM |
|---|---:|---:|---:|---:|---:|---:|---:|
| none | 5 | 7,216 → 6,401 | 211,634 → 151,820 | 5,217 | 630,835 | — | — |
| RV32IM | 5 | 7,216 → 6,341 | 211,885 → 144,912 | 4,840 | 610,204 | 3.27% | — |
| RV32IM + AXI ≤ 2 | 5 | → 6,286 | → 144,495 | 4,785 | 606,827 | 3.81% | 0.55% |
| RV32IM + AXI ≤ 4 | 5 | → 6,286 | → 144,476 | 5,318 | 603,135 | 4.39% | 1.16% |
| RV32IM + AXI ≤ 8 | 5 | → 6,286 | → 144,456 | 4,800 | 604,514 | 4.17% | 0.93% |

At depth 1 the results are almost the same: 6,345 and 6,290 latches. The runs take
about 17 minutes there, against about 80 minutes at depth 5.

An exact latency (`response_latency rd N N`, the same for writes) gives the same
structure as an upper bound:

- N = 2: 6,291 latches and 144,535 AND gates;
- N = 4: 6,290 latches and 144,547 AND gates.

Both are at depth 1.

**The timing increment is small.** The three timing rows give the same 6,286
latches, and their AND counts differ by at most 39. Their areas still spread by
3,700 µm² (0.6%), which is mapping noise from `abc -liberty -fast`. Structurally,
the bounds remove 55 latches (0.9%) and about 420 AND gates (0.3%) beyond RV32IM.

The reasons:

- **MSHR.** CVA6 sizes its MSHR ways to its own load buffer (`mshrWays =
  NrLoadBufEntries` = 2). In an in-order core, the number of outstanding misses is
  capped by the core, not by memory latency.
- **Write buffer.** Entries stay open for coalescing for a configured time, so the
  store rate and that window fill it.
- **Replay table.** It has only 4 entries.

**Validation.** The AIG before and after ABC was co-simulated under stimulus that
satisfies every assumption. Instruction words are legal RV32IM words in all I$
SRAM lanes and AXI read data, with aligned control-flow targets. Neither run
mismatched on any output:

- RV32IM: 3.8M live trace-cycles;
- RV32IM + AXI ≤ 2: 2.3M live trace-cycles.
