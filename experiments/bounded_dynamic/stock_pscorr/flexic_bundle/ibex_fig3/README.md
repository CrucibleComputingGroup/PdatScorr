# Ibex Fig. 3 netlists, regenerated

Paper Fig. 3 shows Ibex area and FMax under three kinds of constraints: register count,
ISA subset and data width. Its netlists were not archived. This folder regenerates the 13
configurations with the paper's experiment checkout and compares each with the values
recorded for the figure. The regenerated netlists are in the FlexIC bundle as
`designs/ibex/fig3_*`.

## Result

`results.csv` compares AND gates, SKY130 area and FMax with the recorded values.

- 11 of the 13 netlists reproduce all three values exactly.
- Two register-count netlists differ slightly:

| Configuration | | AND gates | SKY130 area (µm²) | FMax (MHz) |
|---|---|---|---|---|
| 8 registers | paper | 10931 | 53528.8 | 44.39 |
| | regenerated | 10930 | 53531.3 | 44.43 |
| 4 registers | paper | 9774 | 47314.1 | 48.45 |
| | regenerated | 9774 | 47324.1 | 48.45 |

The areas differ by 0.005% and 0.02%. Against the 32-register reference, the area
reductions are 40.44% and 47.35% in the paper's record, and 40.44% and 47.34% for the
regenerated netlists.

## What was recorded for the paper

The experiment checkout (`experiments/PdatProjectForrocket/PdatScorr` in the workspace)
holds `reg_count_odc_results.csv`, `instruction_subsets_results.csv` and
`register_width_results.csv`. Their rows are the data of the paper's figure script. Each
row gives AND gates, SKY130 area and FMax. No netlist or log of those runs was kept,
except one copy of the No Shifts netlist.

## How to regenerate

```bash
./regenerate.sh      # about 15 min; writes $WS/experiments/ibex_fig3_regen/final
```

The script runs the checkout's own `synth_core.sh` on the constraint files in `dsl/`
and then `tabulate.py`, which writes `results.csv`.

- **ISA subsets:** the constraints only.
- **Register count:** the constraints forbid the unused registers. The flow's ODC
  analysis (`--odc-analysis`) confirms that the affected register-address bits are
  unobservable, replaces the register file by one without the unused registers, and
  synthesizes again. The 32-register point is the run before that step, as in the paper.
- **Data width:** RV32I with a register file whose registers x1–x31 hold 8, 16 or 24
  bits (`make_narrow_regfile.py`, form `writeconcat`).

Environment of the run of 2026-11-09 on ccg-ubuntu:

| Component | Version |
|---|---|
| PdatScorr (flow) | `c523401`, branch `feature/serv`, with the checkout's uncommitted changes |
| PdatRiscvDsl | `b5a5f33`, with the checkout's uncommitted changes |
| Ibex | `1f2232a9` |
| Synlig | `2d838edc9` |
| Yosys | 0.33 |
| ABC | 1.01, compiled 2025-10-07 |
| OpenSTA | 2.7.0 |
| Library | SKY130 HD, typical corner (`sky130_fd_sc_hd__tt_025C_1v80.lib`) |

## How the recipes were established

### ISA subsets

The constraint files were in the checkout. The first run reproduced all five records.

### Data width

The checkout has neither the modified register file nor a working script for it.
`scripts/apply_narrow_register_constraints.py` states the intent, to tie the upper bits
of the registers to zero, but the statement it looks for does not occur in Ibex's
register file.

- **Constraint file:** the 32-bit record (17946 AND gates) is reproduced by
  `require RV32I`. The newer syntax, `include RV32I`, gives 17971.
- **Register file:** 11 ways of writing the narrowing were tried at 8 bits
  (`explore_width_form.sh`, `width_forms.csv`). They give 9531 to 9690 AND gates. One of
  them, `writeconcat`, reproduces the record exactly (9545 gates, 47125.2 µm², 44.32 MHz):

  ```systemverilog
  rf_reg_q <= {{(DataWidth-8){1'b0}}, wdata_a_i[7:0]};
  ```

  The same form reproduces the 16- and 24-bit records exactly.

### Register count

The flow's ODC step, as committed in the checkout, reproduces the 16-register record
exactly. For 8 and 4 registers it gives the values in the table above. Three checks
were made:

- **Repeatability:** ABC writes a differently ordered netlist file on most runs, but the
  values do not vary (`repeat_odc_abc.sh`). For 4 registers, 40 repetitions of the ABC
  step on the same input gave 9774 AND gates and 47324.1376 µm² every time. For 8
  registers, 24 repetitions gave 9 distinct netlist files, all with 10930 AND gates and
  53531.3408 µm².
- **ABC build:** the ABC shipped with Yosys 0.33 gives the same AND counts.
- **Earlier register-file form:** the checkout's Surelog cache preserves the optimized
  register file of a 4-register run of 2025-11-07, before the committed version of the
  ODC script. That form is further from the record: 9705 AND gates for 4 registers,
  10859 for 8 and 13255 for 16 (`make_regcount_regfile.py`, `odc_resynth.sh`).

The cause of the remaining difference was not found.

## Search for the original netlists

Before regenerating, the original author's folders on ccg-rhel and ccg-ubuntu and this
workspace were searched in two ways: by the recorded areas in the flow's area files and
gate logs, and by the recorded AND count in the header of every `.aig` file. Only the
No Shifts netlist was found (17270 AND gates).

## Files

| File | Purpose |
|---|---|
| `regenerate.sh` | regenerates the 13 netlists and checks them |
| `tabulate.py` | compares a regenerated folder with the paper's record |
| `results.csv` | that comparison for the run in the bundle |
| `dsl/` | the constraint files; `reg_count/` and `isa_subsets/` are copies from the checkout |
| `make_narrow_regfile.py` | writes the narrowed register file, in any of the forms tried |
| `explore_width_form.sh`, `width_forms.csv` | the search for the data-width form |
| `repeat_odc_abc.sh` | repeatability of the ABC step |
| `make_regcount_regfile.py`, `odc_resynth.sh` | the earlier register-file form |
