# Paper Table 1 (single-cycle core, RISSP against PwF): audit and regeneration

Paper Table 1 compares core area for the 16 subsets of the multiply, divide, add and
shift instructions on a single-cycle RV32E core: a module-level column labelled RISSP and
a PwF column. This folder traces both columns to their runs, records what is wrong with
them, and regenerates the comparison on a core whose instructions work.

## Result

The published advantage of PwF (44–50% with the divider present, 22% with every unit
present) comes from a divider that does not work in any netlist of the table. On a
corrected core:

- **PwF with error injection matches module-level removal** in every subset, from the
  complete core and without unit switches in the RTL: its area is within 1.87% in 15
  subsets and 5.79% larger in one, and AND gates differ by −0.34% to +0.17%.
  The outlier, Mul+Add+Shift, has an AND-gate difference of −0.02% and is noise of the
  technology mapper: with ABC's default mapping instead of the flow's `-fast`, the same
  two netlists map to 73,731 µm² (baseline) and 72,404 µm² (PwF).
- **Pruning constant and equal signals only** (constraint and sweep without error
  injection, which is how the published PwF column was produced) removes the shifter
  and, when multiply and divide are both forbidden, the multiply/divide unit. When one
  of the two is kept, it removes neither: the core is +29.8% to +61.6% against the
  baseline in these eight subsets, and −0.4% to +4.0% in the other eight.

| Subset (Mul Div Add Shift) | Published RISSP | Published PwF | RISSP (module-level) | PDAG† (sweep only) | PwF | PDAG† against RISSP | PwF against RISSP |
|---|---|---|---|---|---|---|---|
| none | 33148.04 | 32205.90 | 30994.73 | 32237.17 | 30993.48 | +4.0% | +0.00% |
| Shift | 36862.85 | 35661.70 | 34321.67 | 35621.66 | 34381.72 | +3.8% | +0.17% |
| Add | 35940.72 | 32205.90 | 32362.29 | 32406.08 | 32153.34 | +0.1% | −0.65% |
| Add, Shift | 39303.95 | 35609.20 | 35733.02 | 35708.00 | 35645.44 | −0.1% | −0.25% |
| Div | 60857.12 | 31996.90 | 65590.41 | 106010.42 | 64362.98 | +61.6% | −1.87% |
| Div, Shift | 64291.66 | 35521.60 | 68431.88 | 109612.63 | 68674.61 | +60.2% | +0.35% |
| Div, Add | 63397.05 | 31950.60 | 65958.26 | 105643.82 | 66602.63 | +60.2% | +0.98% |
| Div, Add, Shift | 66939.20 | 35376.40 | 69639.29 | 109272.30 | 70187.32 | +56.9% | +0.79% |
| Mul | 85254.27 | 77455.50 | 78507.80 | 106249.40 | 78371.41 | +35.3% | −0.17% |
| Mul, Shift | 82890.75 | 81249.20 | 83830.40 | 110118.11 | 82353.98 | +31.4% | −1.76% |
| Mul, Add | 85784.77 | 77583.20 | 80069.29 | 105378.57 | 80016.74 | +31.6% | −0.07% |
| Mul, Add, Shift | 88697.57 | 80835.00 | 83948.01 | 108944.49 | 88810.18 | +29.8% | +5.79% |
| Mul, Div | 81197.88 | 77586.90 | 105174.62 | 106424.57 | 104487.71 | +1.2% | −0.65% |
| Mul, Div, Shift | 83980.54 | 80808.80 | 107799.64 | 109213.49 | 107983.56 | +1.3% | +0.17% |
| Mul, Div, Add | 100503.89 | 77327.90 | 105637.56 | 105753.93 | 105733.91 | +0.1% | +0.09% |
| all | 104164.90 | 80835.00 | 109648.91 | 109217.25 | 109217.25 | −0.4% | −0.39% |

Areas are SKY130 HD in µm²; the last two columns are relative to the corrected baseline.
The three corrected columns are the paper's Table 1 (`results/corrected_core.csv`). All
48 netlists pass the instruction-level test on the instructions of their own subset.

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
- **Sweep only** (PDAG† in the paper's table): the checkout's `synth_core.sh --core
  riscvsinglecycle --gates`, unchanged, on the corrected core with all units present. It
  prunes constant and equal signals under the constraint.
- **PwF**: the same, with the error-injection step of the next section before the sweep.

All three use the same mapping and observation boundary, and the two PwF columns the
same constraint.

**The constraint and reset.** The flow generates the constraint as
`!rst_n || permitted(instruction)`: it exempts the cycles in which reset is asserted.
The paper's table uses the constraint without this exemption, so that it holds in every
cycle (`run_pwf_inreset.sh` removes `!rst_n ||` from the generated assumption). The
reason is the sweep-only column in the four subsets without multiply and divide. There
the unit's select is constant outside reset, but during reset the registers read as
zero and a division by zero returns all ones, so the unit's result is not constant and
the sweep keeps the unit: 104,335, 86,644, 82,980, 86,454 µm². This is an
effect of the exemption, not of pruning constant and equal signals. Both variants are
tabulated: `results/corrected_core.csv` (every cycle) and
`results/corrected_core_reset_exempt.csv` (as generated). The PwF column differs by at
most 1.23% between them, and every candidate is accepted in both.

## Error injection

`error_injection/` applies the paper's microarchitecture-aware error injection
(Section 4.2) to this core. The ODC step of the experiment checkout is not used: its
monitor code is specific to Ibex and fails to parse for this core, and it knows only the
multiply/divide unit as a whole.

- **Microarchitecture description** (`microarchitecture.json`): the four unit results
  that enter the result multiplexers (`mul_result`, `div_result`, the subtract/compare
  result `adder_result`, `shifter_result`) with the instructions that select each, and
  the observation boundary: instruction address and data-memory strobes in every cycle,
  data-memory address and write data in the cycles with a request. The register file is
  state and is covered by the sequential proof.
- **Candidates**: the unit results whose instructions the constraint forbids entirely.
- **Injection** (`inject.py`): each candidate is forced to 0 in the netlist, after
  `proc` in the flow's own Yosys script.
- **Proof** (`miter.py`): the product of the original and the injected core, both from
  the reset state and under the constraint, has one output per observed bit that is 1
  when the two disagree. ABC's `scorr` on the product proves by 1-induction that every
  such output is constant 0; otherwise the candidate is rejected.
- **Simulation check** (`crosscheck.py`): independent of the proof, the same product is
  simulated with random permitted instructions, random memory data and reset pulses,
  during which the instruction is arbitrary if the constraint exempts reset. This is
  finite evidence, not a proof.

Outcome (`results/error_injection.csv`): in all 15 subsets with a candidate, every
candidate is accepted by one joint proof. ABC needs 22–52 s for it; the whole step,
with the synthesis of the injected core, takes 26–84 s. At least 25,600 simulated
instructions per subset show no disagreement. With the constraint as generated the
outcome is the same (22–45 s in ABC).

With the data-memory address observed in every cycle (`inject.py --strict`), the
injection at the subtract/compare result is rejected: the control unit requests a
subtraction during branches, and its result reaches the address output although no
request is made. For Mul+Div, with the constraint as generated, this leaves 105,555 µm²
instead of 104,384 µm².

Negative controls (`results/error_injection_controls.csv`): in every subset, an
injection at each unit whose instructions are permitted, and at the address adder, must
be rejected. All 48 controls (32 at units, 16 at the address adder) are rejected by
the proof, none by its time limit, and the simulation finds a disagreement in every one. The
same holds for the 48 controls with the constraint as generated. A rejected proof takes
longer than an accepted one: median 81 s, at most 15 minutes.

## The instruction-level test

`tools/coretest.py` drives an AIG with concrete instructions and compares against an
RV32 reference: register results (read back through `SW` on the data output), load and
store addresses and strobes, and the next PC of branches and jumps. It covers 46
instruction classes with at least 128 operand pairs each, and applies only `LW`, `SW` and the
instruction under test, so a netlist optimized under a constraint can be tested on its
own subset. `tools/aigsim.py` is the bit-parallel AIG simulator underneath.

## How to regenerate

```bash
./regenerate.sh      # writes $WS/experiments/rissp_table_regen/final
```

The script assembles the three cores, runs the PwF flow on each, the baseline and the
error-injection step on the corrected one, and writes `results/*.csv`. The synthesis
runs take about 5 minutes and the accepted injections about 5 more per constraint; the
negative controls, whose proofs must fail, take up to 15 minutes each.

| File | Content |
|---|---|
| `results/published_rissp_column.csv` | the 16 saved baseline netlists: area, AND gates, logic depth, failing instructions |
| `results/published_pwf_column.csv` | PwF on the paper-era core: published and regenerated area, failing instructions |
| `results/minfix_pwf.csv` | PwF on the core with only the divider's `case` rewritten |
| `results/corrected_core.csv` | the paper's Table 1: baseline, sweep only and PwF on the corrected core, constraint in every cycle |
| `results/error_injection.csv` | per subset: candidates, accepted injections, proof time, simulation check |
| `results/error_injection_controls.csv` | the negative controls of the proof |
| `results/*_reset_exempt.csv` | the same three tables with the constraint as generated, which exempts reset |

Environment of the run of 2026-11-17 on ccg-ubuntu: PdatScorr `c523401` with the
checkout's uncommitted changes, PdatRiscvDsl `b5a5f33` with the checkout's uncommitted
changes, Synlig `2d838edc9`, Yosys 0.33, ABC 1.01 (compiled 2025-10-07), SKY130 HD
typical corner.
