# Mechanism: interface wait-time bounds remove unused table entries

This test asks whether Pscorr's own technique, CRISP → SVA → ABC `scorr`, can turn
a memory wait-time bound into deleted storage.

The test design is [`ldq.sv`](ldq.sv), an 8-entry table of outstanding loads:

- the lowest free entry is allocated first;
- each request carries its entry index as a tag;
- responses may return out of order;
- the capacity is a parameter, and it is never changed.

[`ldq_top.sv`](ldq_top.sv) wraps it with its writeback always accepted. Every
constrained run uses the stock Yosys commands and the stock ABC command.

## Result

| Assumption on the memory port | Latches kept (of 272) |
|---|---:|
| none | 272 |
| stock CRISP timing template (bounds the request-acceptance stall) | 272 |
| per-tag response latency ≤ 2 | 175 |

The per-tag latency bound is what makes the difference. The stock timing template
counts how long a request waits to be accepted. It does not bound how long an
accepted request waits for its response, and that wait is what limits occupancy.

With the latency bound written by the extended CRISP generator, and with reset
assumed in the first cycle, `scorr` removes exactly the unreachable entries:

| Response latency ≤ | Entries ever occupied (exact search) | Latches kept, depth 4 |
|---:|---|---:|
| 1 | 0–3 | 141 |
| 2 | 0–4 | 176 |
| 3 | 0–5 | 213 |
| 4 | 0–6 | 248 |

- Each entry has 34 latches. The few extra latches are monitor latches that
  `scorr` kept as representatives.
- [`ldq_reach.py`](ldq_reach.py) computes the exact reachable control states from
  reset by explicit-state search.
- Bounds 3 and 4 need induction depth 4; bounds 1 and 2 already succeed at depth 1.

## CRISP

[`ldq_crisp.yaml`](ldq_crisp.yaml) names the memory port as a channel. The
declaration files are `ldq_lat<N>.dsl`, for example:

```
version 2
grant_latency mem 0
response_latency mem 2
```

The generator lives in PdatRiscvDsl, branch `feat/bounded-dynamic-crisp`, file
`pdat_dsl/channel_timing.py`. It emits one age monitor per tag, and assumes that:

- responses come only for outstanding tags;
- an outstanding request at its deadline is answered.

## Initial-state semantics

The stock ABC command begins with `cycle 100`. That command takes the state reached
by a random, unconstrained 100-cycle simulation as the new initial state.

The outcome therefore depends on that random run. With the same depth and the same
bound, a structurally different but equivalent monitor gave 280 latches at bound 2
instead of 175.

The flow used from here on drops `cycle 100` and assumes reset in the first cycle,
which leaves reset free afterwards. Results are then deterministic and match the
exact reachable set above.

The `write_aiger -zinit` export gives uninitialized registers arbitrary values in
frame 0, which a one-flop PDR check confirms. Assuming reset in that frame
supplies the reset state.

## Frontends

LEN5 needs yosys-slang, because Synlig cannot parse its `foreach`. On this test
both frontends give the same result: 176/177 latches at bound 2 and 248 at bound 4.

Synlig mis-elaborates `$bits(port)`, so the generator takes tag widths from the
configuration.

## Reproduce

```sh
# first table: hand-written monitors, stock ABC command (with cycle 100)
python3 run_mechanism.py --output <new dir> --variants none STALL_BOUND TAG_LATENCY --depths 1 4
# second table: CRISP-generated monitors, reset-first semantics, no cycle 100
python3 run_mechanism_crisp.py --output <new dir>                  # Synlig
python3 run_mechanism_crisp.py --frontend slang --depths 4 --output <new dir>
python3 ldq_reach.py --lats 1 2 3 4                                 # exact reachable entries
```

The recorded runs are `mech_v1` (first table) and `mech_crisp_reset_final_v1` and
`mech_crisp_reset_final_slang_v1` (second table, with `reach.jsonl`). They are under
`/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/stock_pscorr/build`.
