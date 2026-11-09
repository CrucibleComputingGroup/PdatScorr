# FlexIC results

`results.csv` and `summary.txt` are the output of `run_all.py` for all 70 designs of this
bundle, mapped to the FlexIC Gen3 standard-cell library G3SC_T5 v1.0.1 (typical corner,
1.5 V, 25 °C).

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
