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

(filled in as runs complete; see the per-core sections below)
