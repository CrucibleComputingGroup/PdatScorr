# ScorrPdat - RTL Scorecard and Synthesis Optimization

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

### RTL-Scorr (SMT-based equivalence checking)

```bash
cd rtl_scorr
./rtl_scorr_ibex_full.sh <dsl_file> [output_dir]
```

Full RTL-level signal correspondence with SMT proving and cone extraction.

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

### Batch Comparison

```bash
./batch_compare_simple.sh <dsl_file> [output_dir]
```

Runs parallel comparison of ISA-only vs ISA+timing across multiple ABC depths.
- Tests depths 2, 3, 4, 5
- Includes both 2-stage and 3-stage pipeline variants
- Generates CSV with chip area (µm²) for each configuration

## ABC Scorr Tuning

The `scorr` command has been tuned for stability across different k-induction depths:

```bash
scorr -c -m -F <depth> -C 10000 -S 10 -X 3 -v
```

**Key parameters:**
- `-C 10000`: Conflict limit (10x default) - critical for higher depths
- `-S 10`: Simulation frames for counter-examples (5x default)
- `-X 3`: Stop after 3 iterations of no improvement
- `-m`: Full merge mode with constraints

**Why tuning matters:**
Default `-C 1000` is too low for depth ≥4, causing area to increase instead of decrease. Higher conflict limits ensure ABC doesn't give up prematurely when searching for register equivalences.

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
- **CoreSim** - Simulation framework (for generating VCDs/JSONs)
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
- **CoreSim** - Processor simulation framework --- includes Ibex core as submodule
- **RtlScorr** - Yosys plugin for formal verification
