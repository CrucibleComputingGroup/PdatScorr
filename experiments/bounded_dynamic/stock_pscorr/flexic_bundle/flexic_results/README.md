# FlexIC results

`results.csv` and `summary.txt` are the output of `run_all.py` for the 70 Rocket, CVA6 and
Ibex Table 4 designs of this bundle, mapped to the FlexIC Gen3 standard-cell library
G3SC_T5 v1.0.1 (typical corner, 1.5 V, 25 °C). The 13 Ibex Fig. 3 designs were mapped
in a second run; see the last section.

The run was made by Jonathan Postelnik on ccg-rhel with Yosys 0.70 (YoWASP build). It
used this bundle's recipe, with ABC's `strash; dretime; map` written out explicitly; that
is the script `abc -fast` runs in Yosys 0.33. The files are as received: `results.csv`
was re-saved with padded columns and CRLF line endings. The mapped netlists and logs are
not included.

## Checks

- All 70 designs mapped, with no unmapped cells (the `note` column is empty).
- One Yosys version for all designs.
- The normalized areas recomputed from the raw areas match the file.

## Summary

Reduction against each core's RV32IM reference:

| | FlexIC | SKY130 (paper) |
|---|---|---|
| Rocket, 21 workloads | geomean 9.25%, max 21.98% | 10.14%, 25.94% |
| CVA6, 21 workloads | geomean 3.27%, max 8.12% | 3.45%, 9.14% |
| Ibex Table 4, timing vs no timing | 0.19%, 0.22%, -0.01% | 0.19%, 0.13%, 0.16% |

Flip-flops are a larger share of FlexIC area:

- Rocket reference: 45.6%, against 30.6% in SKY130;
- CVA6 reference: 30.2%, against 20.8%.

For the seven workloads with the largest savings:

- the share of logic removed is similar in both libraries: Rocket 31.9–34.6% against
  31.1–34.3%, CVA6 10.1–10.3% against 10.5–10.8%;
- the share of flip-flops removed is identical: 7.0% (Rocket) and 3.0% (CVA6).

Those reductions are therefore smaller in FlexIC. For the other workloads, the two
libraries differ by at most 1.4 percentage points.

## Ibex Fig. 3

`fig3_summary.txt` is the `summary.txt` of `run_all.py --only ibex/fig3` with the same
library, run on ccg-rhel on 2026-11-09 and received as pasted text. `results.csv`, the
mapped netlists and the logs were not received, and the Yosys version of this run was
not recorded.

Checks:

- All 13 designs mapped, with no unmapped cells.
- The 32-bit reference has the same area, 5989280, as Table 4's RV32I without timing in
  the first run; the two are the same configuration.
- The normalized areas recomputed from the areas match the file.

Reduction against each group's reference:

| Group | Configuration | FlexIC | SKY130 (paper) |
|---|---|---|---|
| Registers (vs 32) | 16 | 29.55% | 27.15% |
| | 8 | 44.00% | 40.44% |
| | 4 | 50.89% | 47.35% |
| ISA subset (vs RV32IM) | RV32I | 24.46% | 28.77% |
| | No Shifts | 25.48% | 30.69% |
| | No Branches | 24.74% | 28.95% |
| | Arith Only | 31.54% | 34.69% |
| Data width (vs 32-bit) | 24-bit | 15.77% | 15.71% |
| | 16-bit | 32.41% | 31.00% |
| | 8-bit | 48.82% | 47.55% |

The 8- and 4-register netlists are regenerated netlists whose SKY130 areas differ from
the paper's record by 0.005% and 0.02% (`../ibex_fig3/README.md`).

Flip-flops are a larger share of FlexIC area here as well. The first run's log for the
same Ibex configuration shows one flip-flop cell, `DFF_X1PC_T5`, of area 1920. With the
flip-flop counts of the SKY130-mapped netlists:

- 32-register core: flip-flops are 51.6% of the area, against 35.9% in SKY130;
- RV32IM core: 42.4%, against 27.8%.

This explains the direction of the differences:

- 4 registers: the reduction is 28.7 points of flip-flops and 22.2 of logic in FlexIC,
  against 20.0 and 27.4 in SKY130;
- arithmetic only: 5.1 points of flip-flops and 26.4 of logic, against 3.4 and 31.3;
- 8-bit data: 26.2 points of flip-flops and 22.6 of logic, against 18.2 and 29.4.
