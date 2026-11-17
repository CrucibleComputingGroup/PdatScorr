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
  complete core and without unit switches in the RTL: +0.24% in area on geometric mean
  (−1.7% to +5.8%), and −0.26% to +0.18% in AND gates. The largest area
  difference, +5.8% for Mul+Add+Shift, comes with an AND-gate difference of −0.02% and
  is noise of the technology mapper: with ABC's default mapping instead of the flow's
  `-fast`, the same two netlists map to 73,731 µm² (baseline) and 72,404 µm² (PwF).
- **PwF without error injection** (constraint and sweep only, which is how the published
  column was produced) removes the shifter, but neither the multiplier nor the divider:
  it is −0.5% to +236.6% against the baseline.

| Subset (Mul Div Add Shift) | Published RISSP | Published PwF | Corrected baseline | PwF without error injection | PwF | Without injection, against baseline | PwF against baseline |
|---|---|---|---|---|---|---|---|
| none | 33148.04 | 32205.90 | 30994.73 | 104335.07 | 30965.95 | +236.6% | −0.1% |
| Shift | 36862.85 | 35661.70 | 34321.67 | 86644.35 | 34372.97 | +152.4% | +0.1% |
| Add | 35940.72 | 32205.90 | 32362.29 | 82979.58 | 32153.34 | +156.4% | −0.7% |
| Add, Shift | 39303.95 | 35609.20 | 35733.02 | 86454.17 | 35645.44 | +141.9% | −0.2% |
| Div | 60857.12 | 31996.90 | 65590.41 | 106195.60 | 64667.02 | +61.9% | −1.4% |
| Div, Shift | 64291.66 | 35521.60 | 68431.88 | 109314.84 | 68689.63 | +59.7% | +0.4% |
| Div, Add | 63397.05 | 31950.60 | 65958.26 | 105750.17 | 66616.39 | +60.3% | +1.0% |
| Div, Add, Shift | 66939.20 | 35376.40 | 69639.29 | 109272.30 | 70098.48 | +56.9% | +0.7% |
| Mul | 85254.27 | 77455.50 | 78507.80 | 106225.63 | 79344.85 | +35.3% | +1.1% |
| Mul, Shift | 82890.75 | 81249.20 | 83830.40 | 110528.51 | 82386.52 | +31.9% | −1.7% |
| Mul, Add | 85784.77 | 77583.20 | 80069.29 | 105419.86 | 80036.76 | +31.7% | −0.0% |
| Mul, Add, Shift | 88697.57 | 80835.00 | 83948.01 | 108761.81 | 88810.18 | +29.6% | +5.8% |
| Mul, Div | 81197.88 | 77586.90 | 105174.62 | 106429.57 | 104383.86 | +1.2% | −0.8% |
| Mul, Div, Shift | 83980.54 | 80808.80 | 107799.64 | 109309.84 | 108153.73 | +1.4% | +0.3% |
| Mul, Div, Add | 100503.89 | 77327.90 | 105637.56 | 105767.69 | 105645.07 | +0.1% | +0.0% |
| all | 104164.90 | 80835.00 | 109648.91 | 109122.16 | 109122.16 | −0.5% | −0.5% |

Areas are SKY130 HD in µm²; the last two columns are relative to the corrected baseline.
The corrected columns are in `results/corrected_core.csv`. All 48 corrected netlists pass
the instruction-level test on the instructions of their own subset.

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
- **PwF without error injection**: the checkout's `synth_core.sh --core riscvsinglecycle
  --gates`, unchanged, on the corrected core with all units present.
- **PwF**: the same, with the error-injection step of the next section before the sweep.

All three use the same mapping and observation boundary, and the two PwF columns the
same generated constraint. The constraint has the form
`!rst_n || permitted(instruction)`: it exempts the cycles in which reset is asserted.
This matters for the sweep-only column in the four subsets without multiply and divide.
There the unit's select is constant outside reset, but during reset the registers read
as zero and a division by zero returns all ones, so the unit's result is not constant
and the sweep keeps the unit (83,000–104,000 µm²). With the constraint also holding
during reset (`run_pwf_inreset.sh`), the sweep alone reaches 32,237, 35,622, 32,406 and
35,708 µm² in these four subsets (`results/sweep_constraint_in_reset.csv`); the other
twelve change by at most 0.4%. Error injection does not depend on this.

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
  simulated with random permitted instructions, random memory data and reset pulses with
  arbitrary instructions. This is finite evidence, not a proof.

Outcome (`results/error_injection.csv`): in all 15 subsets with a candidate, every
candidate is accepted by one joint proof (27–76 s including the synthesis of the
injected core), and about 25,000 simulated instructions per subset show no disagreement.

With the data-memory address observed in every cycle (`inject.py --strict`), the
injection at the subtract/compare result is rejected: the control unit requests a
subtraction during branches, and its result reaches the address output although no
request is made. For Mul+Div this leaves 105,555 µm² instead of 104,384 µm².

Negative controls (`results/error_injection_controls.csv`): in every subset, an
injection at each unit whose instructions are permitted, and at the address adder, must
be rejected. All 48 controls (32 at units, 16 at the address adder) are rejected by
the proof itself, none by its time limit, and the simulation finds a disagreement in
every one.

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
runs take about 5 minutes and the accepted injections about 5 more; the negative
controls, whose proofs must fail, take up to 15 minutes each (median 78 s).

| File | Content |
|---|---|
| `results/published_rissp_column.csv` | the 16 saved baseline netlists: area, AND gates, logic depth, failing instructions |
| `results/published_pwf_column.csv` | PwF on the paper-era core: published and regenerated area, failing instructions |
| `results/minfix_pwf.csv` | PwF on the core with only the divider's `case` rewritten |
| `results/corrected_core.csv` | baseline, PwF without error injection and PwF on the corrected core |
| `results/sweep_constraint_in_reset.csv` | PwF without error injection when the constraint also holds during reset |
| `results/error_injection.csv` | per subset: candidates, accepted injections, proof time, simulation check |
| `results/error_injection_controls.csv` | the negative controls of the proof |

Environment of the run of 2026-11-17 on ccg-ubuntu: PdatScorr `c523401` with the
checkout's uncommitted changes, PdatRiscvDsl `b5a5f33` with the checkout's uncommitted
changes, Synlig `2d838edc9`, Yosys 0.33, ABC 1.01 (compiled 2025-10-07), SKY130 HD
typical corner.
