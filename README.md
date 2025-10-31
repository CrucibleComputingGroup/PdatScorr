# ScorrPdat - RTL Scorecard and Synthesis Optimization

[![Regression Tests](https://github.com/CrucibleComputingGroup/PdatScorr/actions/workflows/regression-tests.yml/badge.svg)](https://github.com/CrucibleComputingGroup/PdatScorr/actions/workflows/regression-tests.yml)

Tools for RTL analysis, synthesis optimization, and formal equivalence checking of RISC-V processors with DSL-based instruction constraints.

## Overview

ScorrPdat provides synthesis and analysis tools that work with PDAT DSL specifications to optimize processor designs. It focuses on:

- RTL synthesis with instruction constraints
- ABC-based sequential optimization (scorr)
- SMT-based cone extraction and equivalence proving
- Dead code detection in RTL designs
- Gate-level synthesis integration

## Installation

```bash
# Install dependencies (including pdat-dsl)
pip install -r requirements.txt

# Requires external tools:
# - Synlig (SystemVerilog frontend for Yosys)
# - ABC (sequential optimization)
```

## Usage

### Basic Synthesis with Constraints

```bash
./synth_ibex_with_constraints.sh <dsl_file> [output_dir]
```

Generates optimized Ibex RTLIL with instruction constraints applied.

**Options:**
- `--gates` - Also synthesize to gate-level netlist
- `--3stage` - Enable 3-stage pipeline
- `--abc-depth N` - Set k-induction depth

**Example:**
```bash
./synth_ibex_with_constraints.sh my_rules.dsl --gates --3stage
```

### Data Type Constraints (NEW)

ScorrPdat now supports **data type constraints** from PdatDsl, allowing you to specify operand widths and signedness. This enables powerful optimizations by indicating which bits of operands are actually used.

**Example DSL with data type constraints:**
```dsl
# Require RISC-V extensions
require RV32I
require RV32M

# Allow MUL to only use narrow signed operands (8/16-bit)
# Note: When allowing i16, must also allow i8 (narrower types included)
# Upper 16 bits can be optimized when values are narrow
instruction MUL { dtype = ~(i8 | i16) }

# Allow DIV to use only 8-bit or 16-bit signed values
instruction DIV { dtype = ~(i8 | i16) }

# Per-operand constraints for fine control
instruction MULHU { rs1_dtype = ~(u8 | u16), rs2_dtype = ~(u8 | u16) }
```

**Data type syntax:**
- `i8`, `i16`, `i32`, `i64` - Signed types (sign-extended)
- `u8`, `u16`, `u32`, `u64` - Unsigned types (zero-extended)
- `|` operator - Union of types (e.g., `i8 | u8`)
- `~` prefix - Negation (allow ONLY these types, forbid all others)

**Benefits:**
1. **Hardware Optimization**: Synthesis tools optimize away unused upper bits
2. **ABC Optimization**: Sequential optimization can use narrower data paths
3. **Power Reduction**: Reduced switching activity on unused bits
4. **Documentation**: Captures high-level intent in machine-readable form

See `examples/` for complete examples with data constraints.

### RTL-Scorr (SMT-based equivalence checking)

```bash
cd rtl_scorr
./rtl_scorr_ibex_full.sh <dsl_file> [output_dir]
```

Full RTL-level signal correspondence with SMT proving and cone extraction.

### Batch Synthesis of Multiple DSLs

```bash
./batch_synth.sh [OPTIONS] <dsl_files_or_dirs>...
```

Run multiple DSL synthesis jobs in parallel with automatic result comparison.

**Options:**
- `-j, --jobs N` - Maximum parallel jobs (default: 4)
- `--runs N` - Number of runs per DSL file (default: 1)
- `--gates` - Synthesize to gate-level netlist
- `--3stage` - Enable 3-stage pipeline
- `--abc-depth N` - Set k-induction depth
- `-v, --verbose` - Show detailed output

**Examples:**
```bash
# Process all DSL files in a directory
./batch_synth.sh --gates -j 8 ../PdatDsl/workload/

# Run each DSL 5 times, use best result (handles ABC non-determinism)
./batch_synth.sh --runs 5 -j 40 --gates ../PdatDsl/workload/

# Mix directories and specific files
./batch_synth.sh -j 12 ../PdatDsl/examples/ custom.dsl
```

**Handling Non-Determinism:**

ABC's `scorr` optimization can produce varying results across runs due to SAT solver randomness. The `--runs N` option:
- Runs each DSL N times independently in parallel
- Automatically selects the best result (minimum chip area)
- Organizes outputs in `output/run_1/`, `output/run_2/`, etc.
- Creates `output/dsl_name/best/` symlink to the best run

**Output Structure with `--runs 3`:**
```
output/
  run_1/
    rv32im_no_add/
    rv32im/
    baseline/
  run_2/
    rv32im_no_add/
    ...
  run_3/
    ...
  rv32im_no_add/
    best/ → ../run_2/rv32im_no_add/  (symlink to best run)
  synthesis_comparison.csv  (uses best runs)
```

### Batch Timing Comparison

```bash
./batch_compare_timing.sh <dsl_file> [output_dir] [runs_per_config]
```

Parallel comparison of ISA-only vs ISA+timing across multiple ABC depths and pipeline configurations.

**Parameters:**
- `dsl_file` - DSL specification file
- `output_dir` - Base output directory (default: output/comparison)
- `runs_per_config` - Number of runs per configuration (default: 1)

**Example:**
```bash
# Single run (fast)
./batch_compare_timing.sh ../PdatDsl/workload/rv32im.dsl

# 3 runs per configuration, use best results
./batch_compare_timing.sh ../PdatDsl/workload/rv32im.dsl output/test 3
```

Tests all combinations of:
- ABC depths: 2, 3, 4, 5, 6, 7, 8
- ISA-only vs ISA+timing constraints
- 2-stage vs 3-stage pipeline (depth ≥ 3)

With `--runs N`, each configuration is run N times and the best result is automatically selected.

### Synthesis with Timing Constraints

```bash
./synth_ibex_with_isa_and_timing.sh <dsl_file> [output_dir]
```

Adds timing constraints on top of ISA constraints to further guide ABC optimization.

**What it does:**
- Generates ISA constraints from DSL (same as `synth_ibex_with_constraints.sh`)
- Adds timing bounds on memory latency (instruction fetch ≤5 cycles, data stall ≤4 cycles)
- Provides relational constraints to help ABC prove equivalences

**Trade-offs:**
- **Overhead**: ~6 flip-flops (2 counters × 3 bits) = ~0.14% area overhead
- **Benefit**: Helps ABC prune unreachable states, potentially reducing final area
- **Result quality**: Depends on how well constraints match real hardware timing

**Why explicit counters?**

Synlig/Yosys only supports immediate `assume(expression)` - NOT SVA temporal operators like:
```systemverilog
assume property (@(posedge clk) req |-> ##[0:5] done);  // ❌ Not supported
```

To specify "within N cycles" for ABC optimization, explicit counters are required:
```systemverilog
logic [2:0] counter_q;
always_ff @(posedge clk) begin
  if (req && !done) counter_q <= counter_q + 1;
  else counter_q <= 0;
end
assume(counter_q <= 3'd5);  // ✓ Supported
```

The counters add minimal hardware but enable multi-cycle timing constraints for ABC's `scorr -c` optimization.

## ABC Scorr Tuning

The `scorr` command has been tuned for stability and optimal area reduction:

```bash
scorr -c -m -F <depth> -C 30000 -S 15 -X 5 -v
```

**Key parameters:**
- `-c`: Enable constraint-based optimization (uses AIGER constraint outputs)
- `-m`: Full merge mode with constraints
- `-F <depth>`: K-induction depth (should match pipeline depth: 2 or 3)
- `-C 30000`: Conflict limit (30x default) - critical for deep induction
- `-S 15`: Simulation frames for counter-examples (7.5x default)
- `-X 5`: Slow refinement detector threshold

**Critical: Understanding -X Parameter**

The `-X` parameter is NOT "iterations without improvement". Instead, it's a **slow refinement detector**:
- After 4 iterations, checks if candidate reduction < `4 × X`
- If too slow, **aborts and returns the UNOPTIMIZED circuit**
- Higher X = easier to trigger abort = worse results

**Recommended values:**
- `-X 5`: Good balance (stops if < 20 candidates eliminated over 4 iterations)
- `-X 0` or omit: Disables the check entirely (let scorr run to completion)
- **Avoid `-X 10+`**: Too easy to abort, returns unoptimized circuits

**Why tuning matters:**
- Default `-C 1000` is too low for depth ≥3, causing incomplete optimization
- Constraint-based optimization requires more SAT solver conflicts
- Higher conflict limits ensure ABC finds all register equivalences
- Proper `-X` tuning prevents premature termination

**Constraint Removal:**
After optimization with constraints, use:
```bash
constr -r; removepo -N <num_real_outputs>; rewrite -l; balance -l
```

- `constr -r`: Converts constraints back to regular outputs
- `removepo -N <N>`: Removes the last N outputs (constraint outputs)
- `rewrite -l; balance -l`: Re-optimize while preserving logic depth

## Directory Structure

```
ScorrPdat/
├── scripts/                  # Core analysis tools
│   ├── inject_checker.py    # Inject assumptions into RTL
│   ├── make_synthesis_script.py
│   ├── detect_rtl_dead_code.py
│   ├── rtl_dead_code_report.py
│   └── synth_to_gates.sh
├── rtl_scorr/               # RTL signal correspondence tools
│   ├── scripts/             # SMT analysis and cone extraction
│   │   ├── smt_check_constant.py
│   │   ├── smt_cone_extractor_v2.py
│   │   ├── extract_cone_*.py
│   │   └── parse_yosys_smt2.py
│   └── *.sh                 # Example workflows
├── synth_ibex_with_constraints.sh  # Main synthesis script
├── requirements.txt
└── README.md
```

## Key Scripts

### Synthesis & Optimization
- `synth_ibex_with_constraints.sh` - ISA constraints only (main entry point)
- `synth_ibex_with_isa_and_timing.sh` - ISA + timing constraints
- `batch_compare_simple.sh` - Parallel comparison across ABC depths
- `scripts/inject_checker.py` - Inject DSL-generated assumptions into RTL
- `scripts/make_synthesis_script.py` - Generate Yosys synthesis scripts
- `scripts/synth_to_gates.sh` - Gate-level synthesis with SKY130

### RTL Analysis
- `scripts/detect_rtl_dead_code.py` - Find unused logic
- `scripts/rtl_dead_code_report.py` - Generate dead code reports
- `scripts/check_signal_constants.py` - Identify constant signals

### SMT-Based Verification
- `rtl_scorr/scripts/smt_check_constant.py` - Verify signals are constant
- `rtl_scorr/scripts/smt_cone_extractor_v2.py` - Extract logic cones
- `rtl_scorr/scripts/smt_prove_equivalences.py` - Prove signal equivalences
- `rtl_scorr/scripts/parse_yosys_smt2.py` - Parse Yosys SMT2 output

## Dependencies

### External Projects
- **PdatDsl** - DSL parser and code generation (installed via requirements.txt)
- **CoreSim/PdatCoreSim** - Simulation framework with Ibex core (auto-detected from ../PdatCoreSim or ../CoreSim)
- **RtlScorr** - Yosys plugin for signal correspondence (separate repo)

### System Tools
- **Synlig** - SystemVerilog frontend for Yosys
- **ABC** - Sequential logic optimization
- **Z3** - SMT solver (for some scripts)

## Workflow Integration

### Overall Architecture
```
PdatDsl → ScorrPdat → Optimized RTL → ABC → Gate-level
   ↓                      ↓
CoreSim → VCDs → RtlScorr → Proven Equivalences
```

### Detailed Synthesis Flow (with Timing Constraints)

```
┌─────────────────────────────────────────────────────────────┐
│ 1. DSL → Assumptions                                         │
│    pdat-dsl codegen rv32im.dsl → assumptions.sv             │
│    (ISA constraints as SystemVerilog assume statements)     │
└────────────────────┬────────────────────────────────────────┘
                     │
┌────────────────────▼────────────────────────────────────────┐
│ 2. Add Timing Constraints (if using timing script)          │
│    Appends counter logic + timing assumptions               │
│    (Overhead: ~6 flip-flops, enables multi-cycle bounds)    │
└────────────────────┬────────────────────────────────────────┘
                     │
┌────────────────────▼────────────────────────────────────────┐
│ 3. Inject into Ibex RTL                                     │
│    inject_checker.py → ibex_id_stage.sv (modified)          │
└────────────────────┬────────────────────────────────────────┘
                     │
┌────────────────────▼────────────────────────────────────────┐
│ 4. SYNLIG - SystemVerilog → AIGER                           │
│    synlig -s synth.ys                                       │
│    • Converts assume() → AIGER constraint outputs (c=N)     │
│    • Result: i/o = 1338/432(c=1) for ISA-only              │
│    • Result: i/o = 1344/434(c=3) for ISA+timing            │
└────────────────────┬────────────────────────────────────────┘
                     │
┌────────────────────▼────────────────────────────────────────┐
│ 5. ABC - Sequential Optimization with Constraints           │
│    abc -c "scorr -c -m -F <depth> -C 10000 -S 10 -X 3"     │
│    • Uses constraints to find register equivalences         │
│    • Removes redundant logic                                │
│    • Tuned parameters for stability across depths           │
└────────────────────┬────────────────────────────────────────┘
                     │
┌────────────────────▼────────────────────────────────────────┐
│ 6. Gate-Level Synthesis (optional, with --gates)            │
│    yosys/synlig + abc -liberty sky130.lib                   │
│    • Maps to standard cells                                 │
│    • Outputs chip area in µm²                               │
└─────────────────────────────────────────────────────────────┘
```

**Key Insight:** Synlig doesn't support SVA temporal operators (`##[0:5]`), only immediate `assume()`. This is why explicit counters are needed for multi-cycle timing constraints.

## Example Workflow

```bash
# 1. Use PdatDsl to create specification
cd ../PdatDsl
pdat-dsl parse my_spec.dsl

# 2. Synthesize with ScorrPdat
cd ../ScorrPdat
./synth_ibex_with_constraints.sh my_spec.dsl --gates

# 3. (Optional) Run simulation to find equivalences
cd ../CoreSim
./run_ibex_random.sh testbenches/ibex/dsls/my_spec.dsl --constants-only

# 4. (Optional) Verify with RtlScorr plugin
cd ../RtlScorr
# Use generated JSONs from CoreSim
```

## License

CC-BY-NC-SA-4.0 - Copyright 2025 Nathan Bleier (nbleier@umich.edu)

Free for non-commercial use. Contact for commercial licensing.

## Related Projects

- **PdatDsl** - ISA subset specification DSL
- **CoreSim/PdatCoreSim** - Processor simulation framework --- includes Ibex core as submodule
- **RtlScorr** - Yosys plugin for formal verification

## Configuration

**Ibex Core Path:** The scripts automatically detect the Ibex core location:
1. If `IBEX_ROOT` environment variable is set, uses that path
2. Otherwise, checks for `../PdatCoreSim/cores/ibex`
3. Falls back to `../CoreSim/cores/ibex`
4. Errors if none are found

To use a custom location:
```bash
export IBEX_ROOT=/path/to/your/ibex
./synth_ibex_with_constraints.sh my_rules.dsl
```
