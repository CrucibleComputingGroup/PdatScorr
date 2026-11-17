# Paper Table 1 (single-cycle core, RISSP against PwF): audit and regeneration

Paper Table 1 compares core area for the 16 subsets of the multiply, divide, add and
shift instructions on a single-cycle RV32E core: a module-level column labelled RISSP and
a PwF column. This folder traces both columns to their runs, records what is wrong with
them, and regenerates the comparison on a core whose instructions work.

## Result

The published advantage of PwF (44–50% with the divider present, 22% with every unit
present) comes from a divider that does not work in any netlist of the table. On a
corrected core, PwF as it was run for the table is never smaller than the module-level
baseline.

| Subset (Mul Div Add Shift) | Published RISSP | Published PwF | Corrected baseline | Corrected PwF | PwF against baseline |
|---|---|---|---|---|---|
| none | 33148.04 | 32205.90 | 30994.73 | 104335.07 | +236.6% |
| Shift | 36862.85 | 35661.70 | 34321.67 | 86644.35 | +152.4% |
| Add | 35940.72 | 32205.90 | 32362.29 | 82979.58 | +156.4% |
| Add, Shift | 39303.95 | 35609.20 | 35733.02 | 86454.17 | +141.9% |
| Div | 60857.12 | 31996.90 | 65590.41 | 106195.60 | +61.9% |
| Div, Shift | 64291.66 | 35521.60 | 68431.88 | 109314.84 | +59.7% |
| Div, Add | 63397.05 | 31950.60 | 65958.26 | 105750.17 | +60.3% |
| Div, Add, Shift | 66939.20 | 35376.40 | 69639.29 | 109272.30 | +56.9% |
| Mul | 85254.27 | 77455.50 | 78507.80 | 106225.63 | +35.3% |
| Mul, Shift | 82890.75 | 81249.20 | 83830.40 | 110528.51 | +31.9% |
| Mul, Add | 85784.77 | 77583.20 | 80069.29 | 105419.86 | +31.7% |
| Mul, Add, Shift | 88697.57 | 80835.00 | 83948.01 | 108761.81 | +29.6% |
| Mul, Div | 81197.88 | 77586.90 | 105174.62 | 106429.57 | +1.2% |
| Mul, Div, Shift | 83980.54 | 80808.80 | 107799.64 | 109309.84 | +1.4% |
| Mul, Div, Add | 100503.89 | 77327.90 | 105637.56 | 105767.69 | +0.1% |
| all | 104164.90 | 80835.00 | 109648.91 | 109122.16 | −0.5% |

Areas are SKY130 HD in µm². The corrected columns are in `results/corrected_core.csv`;
all 32 corrected netlists pass the instruction-level test on the instructions of their
own subset.

## Where the published numbers come from

Neither column is from the RISSP tool. Both use the lab's own single-cycle core,
`RiscvSingleCycle` (RV32E with the M extension, written in Veryl), at PdatCoreSim commit
`1682660`.

- **RISSP column:** the core with four unit switches (`ENABLE_MUL`, `ENABLE_DIV`,
  `ENABLE_ADDER`, `ENABLE_SHIFTER`), synthesized per subset. The 16 runs are saved in
  `PdatCoreSim/cores/RiscvSingleCycle/synthesis_results/` of the experiment checkout;
  their areas equal the published values (`results/published_rissp_column.csv`).
- **PwF column:** the full core with the CRISP files `experiments/modular_equiv/*.dsl`,
  run through `synth_core.sh --core riscvsinglecycle --gates`. The value is the area
  after the constraint-driven sequential sweep; the flow's ODC step is not in it. Only
  the log of the first subset was kept. Rerunning the flow here reproduces all 16
  published values to the published precision (`results/published_pwf_column.csv`).

## What is wrong with the published table

### 1. The divider is unreachable in every netlist (front end)

Synlig `2d838edc9` mis-elaborates `case (x) inside` statements in two ways: it reads an
item of exactly two values `a, b` as the value range `[a:b]`, and in a range it drops the
top bit of sized constants. The core's divider is written as

```systemverilog
case (op) inside
    OP_DIV, OP_DIVU: ...   // 3'd4, 3'd5  -> elaborated as op == 0, op == 1
    OP_REM, OP_REMU: ...   // 3'd6, 3'd7  -> elaborated as op == 2, op == 3
```

while the result multiplexer after it has four values per item, is elaborated correctly,
and passes the divider's result only for `op` 4–7. The two conditions never overlap, so
`DIV`, `DIVU`, `REM` and `REMU` return 0 in every netlist. Verilator simulates the same
file correctly. `synlig_case_inside/` holds a minimal reproducer with controls: plain
`case`, one value per item, three or more values per item, and the expression form
`x inside {a, b}` are elaborated correctly. The expression form with a range,
`x inside {[a:b]}`, matches only `a`.

Consequences:

- **PwF column:** the divider is dead logic and the sweep removes it in all 16 subsets,
  so the divider costs PwF nothing. With the divider's output constant, the whole
  multiply/divide result is constant whenever multiply is forbidden, which is also what
  let the sweep remove the multiplier.
- **RISSP column:** the baseline's sweep removed the dead divider in two subsets
  (Mul+Div and Mul+Div+Shift: logic depth 87 and 91, against 468–517 in the other six
  Div subsets) and kept it in the other six. Those two rows are about 19,000 µm² below
  their neighbours.

The RTL of Ibex, Rocket and CVA6 contains neither a `case … inside` statement nor a range
in an `inside` expression, so their results are not exposed to this bug.

### 2. The two columns use different ABC scripts

The PwF script starts with `cycle 100`; the baseline script did not. Without it, each of
the 512 uninitialized flip-flops keeps the multiplexer that `write_aiger -zinit` adds to
model its unknown initial value. Rerunning the saved baseline AIGs with `cycle 100` removes
1,039 AND gates from both netlists tried: 4,139 µm² of the 33,148 µm² of the smallest
subset and 4,460 µm² of the 104,165 µm² of the full core. That exceeds PwF's published
margin in five of the eight subsets without a divider.

### 3. "Add absent" removes the address adder in the baseline

`ENABLE_ADDER = 0` ties the adder output to zero for every instruction. Loads and stores
then address location 0, and `LUI`, `AUIPC` and `JALR` give wrong results. The PwF
constraint only forbids the add and compare instructions, and PwF keeps the adder.

### 4. The M extension is incomplete in the RTL

`MULH` and `MULHSU` return 0, and `DIV` and `REM` are computed unsigned.

### 5. Presentation

Two PwF values occur twice (32205.90 and 80835.00), the PwF column is rounded to one
decimal and the RISSP column to two, and the caption says RV32E although the core
includes the M extension.

## The control experiment

`cores/minfix/mdu.sv` is the paper-era unit with one change: the divider's items are
written one value per item, which the front end elaborates correctly. Everything else,
including the paper's PwF flow, is unchanged. PwF's area becomes 86,800–104,200 µm² in
all 16 subsets (`results/minfix_pwf.csv`); it was 32,000–81,200 µm². With a divider that
works, the sweep removes neither the divider nor the multiplier in any subset.

The reason is structural. A unit whose instructions are forbidden still computes on every
instruction and its result is discarded by a multiplexer further on. Its outputs are
unobservable, not constant, and a sweep that merges equivalent nodes cannot remove it.

## The corrected setup

- **Core** (`cores/fixed/`): `mdu.sv` implements all eight M instructions and decodes
  the operation with explicit comparisons; `alu.sv` keeps the adder that forms addresses
  and switches only subtract and compare with `ENABLE_ADDER`. The other files are those
  of commit `1682660`. The M unit agrees with a Verilator reference on 200,000 random
  vectors, and the full core passes all 46 instruction classes of the test.
- **Baseline** (`run_baseline.sh`): the corrected core with its unit switches, through
  the front end, Yosys script, ABC script (`cycle 100` included) and gate mapping of the
  PwF flow. No constraint.
- **PwF**: the checkout's `synth_core.sh --core riscvsinglecycle --gates`, unchanged, on
  the corrected core with all units present.

Not covered: the flow's ODC step. It is not part of the published numbers, and in the
experiment checkout its monitor code is specific to Ibex and fails to parse for this
core. With `ENABLE_ADDER = 0` the baseline also drops the subtraction that the control
unit requests during branches; the result is unused there, but it does reach the address
output, which PwF must preserve.

## The instruction-level test

`tools/coretest.py` drives an AIG with concrete instructions and compares against an
RV32 reference: register results (read back through `SW` on the data output), load and
store addresses and strobes, and the next PC of branches and jumps. It covers 46
instruction classes with at least 128 operand pairs each, and applies only `LW`, `SW` and the
instruction under test, so a netlist optimized under a constraint can be tested on its
own subset. `tools/aigsim.py` is the bit-parallel AIG simulator underneath.

## How to regenerate

```bash
./regenerate.sh      # about 5 min (64 runs in parallel); writes $WS/experiments/rissp_table_regen/final
```

The script assembles the three cores, runs the PwF flow on each and the baseline on the
corrected one, and writes `results/*.csv`.

| File | Content |
|---|---|
| `results/published_rissp_column.csv` | the 16 saved baseline netlists: area, AND gates, logic depth, failing instructions |
| `results/published_pwf_column.csv` | PwF on the paper-era core: published and regenerated area, failing instructions |
| `results/minfix_pwf.csv` | PwF on the core with only the divider's `case` rewritten |
| `results/corrected_core.csv` | baseline and PwF on the corrected core |

Environment of the run of 2026-11-17 on ccg-ubuntu: PdatScorr `c523401` with the
checkout's uncommitted changes, PdatRiscvDsl `b5a5f33` with the checkout's uncommitted
changes, Synlig `2d838edc9`, Yosys 0.33, ABC 1.01 (compiled 2025-10-07), SKY130 HD
typical corner.
