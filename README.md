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
- `synth_ibex_with_constraints.sh` - Main entry point for constrained synthesis
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

```
PdatDsl → ScorrPdat → Optimized RTL → ABC → Gate-level
   ↓                      ↓
CoreSim → VCDs → RtlScorr → Proven Equivalences
```

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
