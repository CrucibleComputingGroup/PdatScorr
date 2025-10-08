# PDabcT - Sequential Equivalence-Based Processor Customization

A tool for constraining and optimizing RISC-V processors by outlawing specific instructions. Uses formal methods (SystemVerilog assumptions + ABC's sequential equivalence checking) to automatically remove unused instruction decode logic.

## Features

- **DSL for instruction constraints**: High-level language for specifying which instructions to outlaw
- **Positive constraints with `require`**: Specify valid instruction sets to further constrain the design space
- **Automatic optimization**: Uses ABC's `scorr` (sequential equivalence checking) to remove dead logic
- **Full flow to gates**: Optional synthesis to Skywater 130nm PDK
- **Ibex RISC-V core support**: Currently supports lowRISC's Ibex core

## Quick Start

### 1. Clone and Initialize

```bash
git clone <repository-url>
cd ScorrPdat

# Initialize the Ibex submodule
git submodule update --init --recursive
```

### 2. Prerequisites

- **Synlig** (SystemVerilog frontend for Yosys)
- **ABC** (Berkeley Logic Synthesis tool)
- **Python 3.7+**
- **Optional**: Skywater 130nm PDK (for gate-level synthesis)

### 3. Run Example

```bash
# Synthesize Ibex with M-extension outlawed
./synth_ibex_with_constraints.sh dsls/example_outlawed.dsl output/ibex_no_muldiv

# With gate-level synthesis
./synth_ibex_with_constraints.sh --gates dsls/example_outlawed.dsl output/ibex_no_muldiv
```

## DSL Language

The Domain-Specific Language (DSL) allows you to specify instruction constraints in a human-readable format.

### Syntax

#### 1. **Require Directives** (Positive Constraints)

Specify which instruction extensions are valid. This tells the optimizer that **only** instructions from these extensions should exist in the design.

```dsl
require RV32I
require RV32M
```

This generates a positive constraint: "instruction must be a valid RV32I or RV32M instruction"

Supported extensions:
- `RV32I` - Base integer instruction set
- `RV32M` - Multiply/divide extension
- `RV64I` - 64-bit base instructions
- `RV64M` - 64-bit multiply/divide
- `ZICSR` - CSR instructions
- `PRIV` - Privileged instructions

#### 2. **Register Constraints**

Limit which registers can be used across ALL instructions. This effectively reduces the register file size.

```dsl
# Only allow registers 0-16 (eliminate 17-31)
require_registers x0-x16

# Or with numeric syntax
require_registers 0-16
```

This generates constraints ensuring that for ANY instruction, ALL register fields (rd, rs1, rs2) must be in the allowed range. This allows the optimizer to remove logic for the upper registers.

**Example use case**: Implementing a 16-register subset of RISC-V for area optimization.

#### 3. **Instruction Rules** (Negative Constraints)

Outlaw specific instructions by name:

```dsl
instruction MUL
instruction DIV
instruction REM
```

With field constraints:

```dsl
# Outlaw ADD when destination is x0 (NOP-like behavior)
instruction ADD { rd = x0 }

# Outlaw loads from specific register
instruction LW { rs1 = x10 }
```

#### 4. **Pattern Rules** (Low-Level)

Specify exact bit patterns to outlaw:

```dsl
pattern 0x02000033 mask 0xFE00707F  # MUL instruction encoding
```

### Complete Example

```dsl
# dsls/example_outlawed.dsl

# Specify valid extensions (positive constraints)
require RV32I
require RV32M

# Limit to 17 registers (x0-x16)
require_registers x0-x16

# Outlaw multiply/divide (negative constraints)
instruction MUL
instruction MULH
instruction MULHSU
instruction MULHU
instruction DIV
instruction DIVU
instruction REM
instruction REMU

# Outlaw specific patterns
instruction ADD { rd = x0 }
```

### How Constraints Work

The DSL generates **three types** of SystemVerilog assumptions:

1. **Positive constraints** (from `require`):
   ```systemverilog
   assume (instr == ADD || instr == SUB || instr == LW || ...);
   ```
   Tells ABC: "instruction bits must match a valid encoding"

2. **Register constraints** (from `require_registers`):
   ```systemverilog
   // Format-aware: only constrains fields that are actually registers
   assume (!is_r_type || (rd <= 16 && rs1 <= 16 && rs2 <= 16));  // R-type: all 3
   assume (!is_i_type || (rd <= 16 && rs1 <= 16));              // I-type: rd, rs1
   assume (!is_s_type || (rs1 <= 16 && rs2 <= 16));             // S-type: rs1, rs2
   ```
   Tells ABC: "register fields (when present) must be in allowed range"

3. **Negative constraints** (from `instruction`/`pattern`):
   ```systemverilog
   assume (instr != MUL);
   assume (instr != DIV);
   ```
   Tells ABC: "these specific instructions never appear"

Combined, this allows ABC's `scorr` to:
- Remove decode logic for invalid/garbage instructions
- Remove decode logic for outlawed instructions
- Remove register file entries for unused registers
- Optimize away data paths that are never used

## Synthesis Script

### Usage

```bash
./synth_ibex_with_constraints.sh [OPTIONS] <rules.dsl> [output_dir]
```

### Options

- `--gates` - Also synthesize to gate-level netlist with Skywater PDK
- `--help` - Show help message

### Arguments

- `<rules.dsl>` - DSL file containing instruction constraints
- `[output_dir]` - Output directory (default: `output/`)

### Examples

```bash
# Basic: Generate optimized RTLIL
./synth_ibex_with_constraints.sh dsls/example_outlawed.dsl

# Specify output directory
./synth_ibex_with_constraints.sh dsls/example_outlawed.dsl output/my_design

# Full flow to gates
./synth_ibex_with_constraints.sh --gates dsls/example_outlawed.dsl output/my_design
```

### Output Files

The script generates:

```
output/
├── ibex_optimized_assumptions.sv     # Generated assumption code
├── ibex_optimized_id_stage.sv        # Modified ID stage with assumptions
├── ibex_optimized_synth.ys           # Yosys synthesis script
├── ibex_optimized_yosys.log          # Synthesis log
├── ibex_optimized_pre_abc.aig        # AIGER before ABC optimization
├── ibex_optimized_post_abc.aig       # AIGER after ABC optimization (optimized!)
├── ibex_optimized_abc.log            # ABC optimization log
└── ibex_optimized_gates.v            # Gate-level netlist (if --gates used)
```

### Key Optimization Step: ABC `scorr`

The script runs ABC with:

```bash
abc -c "read_aiger <input>; strash; cycle 100; scorr -c -F 2 -v; dc2; dretime; write_aiger <output>"
```

- `strash` - Converts to AIG (And-Inverter Graph)
- `cycle 100` - **Critical**: Flushes uninitialized state before `scorr`
- `scorr -c -F 2 -v` - Sequential equivalence checking with constraints
  - `-c` - Use constraints from assumptions
  - `-F 2` - Refinement limit
  - `-v` - Verbose
- `dc2` - Combinational optimization
- `dretime` - Retiming optimization

**Result**: The `cycle 100` fix enables 48% reduction in logic (vs. 14% without it)!

## Results

Example optimization results for Ibex with M-extension outlawed:

| Metric | Before | After | Reduction |
|--------|--------|-------|-----------|
| ANDs | 26,178 | 13,591 | **48%** |
| Latches | 942 | 793 | 16% |

Gate-level metrics (Skywater 130nm):
- **Total cells**: 6,839
- **Chip area**: 34,024 µm²

## Project Structure

```
.
├── synth_ibex_with_constraints.sh    # Main synthesis script
├── scripts/                          # Python scripts
│   ├── generate_instruction_checker.py
│   ├── inject_checker.py
│   ├── instruction_dsl_parser.py
│   ├── make_synthesis_script.py
│   ├── riscv_encodings.py
│   └── synth_to_gates.sh
├── dsls/                             # Example DSL files
│   ├── example_outlawed.dsl
│   └── none_outlawed.dsl
├── cores/                            # Processor cores (submodules)
│   └── ibex/
└── output/                           # Generated files (gitignored)
```

## How It Works

1. **Parse DSL** → Extract required extensions and outlawed instructions
2. **Generate Assumptions** → Create SystemVerilog `assume` statements
3. **Inject into Design** → Insert assumptions into Ibex ID stage
4. **Synthesize with Synlig** → Convert to AIGER format with constraints embedded
5. **ABC Optimization** → Use `scorr` to find and remove equivalent logic
6. **Optional: Map to Gates** → Technology mapping with Skywater PDK

The key insight: Formal assumptions about which instructions will never appear allow sequential equivalence checking (`scorr`) to prove that certain logic paths are unreachable, enabling aggressive optimization.

## Advanced Usage

### Custom Output Paths

```bash
# Specify exact output file
./synth_ibex_with_constraints.sh dsls/my_rules.dsl output/custom.il

# All intermediate files go to the same directory as the output
```

### Manual Gate Synthesis

If you've already run the main script, you can manually run gate-level synthesis:

```bash
./scripts/synth_to_gates.sh output/ibex_optimized
```

### Testing DSL Files

Parse and validate DSL syntax:

```bash
python3 scripts/instruction_dsl_parser.py dsls/example_outlawed.dsl -v
```

## Future Work

- Support for other RISC-V cores (CVA6, Rocket, etc.)
- Support for custom instructions/extensions
- Field-programmable instruction sets
- Integration with RISC-V compliance tests

## References

- **Ibex Core**: https://github.com/lowRISC/ibex
- **ABC**: https://github.com/berkeley-abc/abc
- **Synlig**: https://github.com/chipsalliance/synlig
- **Skywater PDK**: https://github.com/google/skywater-pdk

## License

See individual component licenses:
- Ibex: Apache 2.0
- ABC: BSD-like
