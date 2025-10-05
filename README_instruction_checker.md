# RISC-V Instruction Outlawing System

This system allows you to specify which RISC-V instructions should be disallowed in the Ibex core and automatically generates SystemVerilog assertion modules to enforce these constraints.

## Components

### 1. DSL Parser (`instruction_dsl_parser.py`)
Parses the instruction DSL and builds an abstract syntax tree (AST).

### 2. RISC-V Encoding Database (`riscv_encodings.py`)
Contains the encoding information for RISC-V instructions, including:
- RV32I base instruction set
- RV32M multiply/divide extension
- Privileged instructions
- CSR instructions
- Register name mappings

### 3. Code Generator (`generate_instruction_checker.py`)
Converts DSL rules into SystemVerilog assertion modules.

### 4. Wrapper Module (`ibex_core_wrapper.sv`)
Wraps the ibex_core to facilitate binding of the checker module.

## DSL Syntax

The DSL supports two types of rules:

### High-level Instruction Rules

```
instruction <NAME> [ { <field>=<value>, ... } ]
```

Examples:
```
# Outlaw all multiply instructions
instruction MUL
instruction MULH

# Outlaw ADD when destination is x0
instruction ADD { rd = x0 }

# Outlaw stores to stack pointer
instruction SW { rs1 = sp }

# Multiple constraints
instruction ADD { rd = x0, rs1 = x1, rs2 = x2 }
```

### Low-level Pattern Rules

```
pattern <hex_pattern> mask <hex_mask>
```

Example:
```
# Outlaw MUL using raw pattern/mask
pattern 0x02000033 mask 0xFE00707F
```

### Field Names

- `rd` - Destination register
- `rs1` - Source register 1
- `rs2` - Source register 2
- `opcode` - Instruction opcode
- `funct3` - Function code 3
- `funct7` - Function code 7
- `imm` - Immediate value

### Field Values

- Register names: `x0`-`x31`, `zero`, `ra`, `sp`, `gp`, `tp`, `t0`-`t6`, `s0`-`s11`, `a0`-`a7`, `fp`
- Wildcards: `*`, `x`, `_` (means "don't care")
- Numbers: Decimal, hex (`0x...`), or binary (`0b...`)

### Comments

Lines starting with `#` are comments and are ignored.

## Usage

### Step 1: Create a DSL file

Create a file (e.g., `outlawed.dsl`) with your rules:

```dsl
# Outlaw M extension
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

### Step 2: Generate the checker module

```bash
python3 generate_instruction_checker.py outlawed.dsl instr_checker.sv
```

This creates `instr_checker.sv` containing the assertion module.

### Step 3: Create a bind file

Create `checker_bind.sv`:

```systemverilog
// Bind the instruction checker to the Ibex ID stage
bind ibex_core_wrapper.u_ibex_core.id_stage_i instr_outlawed_checker checker_inst (
  .clk_i                  (clk_i),
  .rst_ni                 (rst_ni),
  .instr_valid_i          (instr_valid_i),
  .instr_rdata_i          (instr_rdata_i),
  .instr_is_compressed_i  (instr_is_compressed_i)
);
```

### Step 4: Use in your simulation

Add to your simulation files:
1. The generated checker module: `instr_checker.sv`
2. The wrapper module: `ibex_core_wrapper.sv`
3. The bind file: `checker_bind.sv`

In your simulation, instantiate `ibex_core_wrapper` instead of `ibex_core`.

## Example

See `example_outlawed.dsl` for a complete example that outlaws the M extension.

Generate the checker:
```bash
python3 generate_instruction_checker.py example_outlawed.dsl example_checker.sv
```

## How It Works

1. **Parsing**: The DSL file is tokenized and parsed into an AST
2. **Pattern Generation**: High-level instruction rules are converted to (pattern, mask) pairs
   - The base instruction encoding is looked up in the database
   - Field constraints are applied to modify the pattern and mask
   - Wildcards exclude fields from matching
3. **Code Generation**: SystemVerilog assertions are generated for each pattern
   - Each assertion checks: `(instr & mask) != pattern`
   - Assertions fire on the ID stage when a valid instruction matches

## Pattern/Mask Encoding

The mask indicates which bits must match:
- Mask bit = 1: This bit must match the pattern
- Mask bit = 0: This bit is a "don't care"

Example for MUL:
```
Pattern: 0x02000033
Mask:    0xFE00707F
```

This matches any instruction where:
- Opcode = 0x33 (OP)
- funct3 = 0x0
- funct7 = 0x01 (M extension)
- rd, rs1, rs2 can be any value (mask bits are 0)

## Extending the System

### Adding New Instructions

Edit `riscv_encodings.py` and add to the appropriate dictionary:

```python
"MYINST": InstructionEncoding("MYINST", 0x..., 0x..., "R", R_TYPE_FIELDS),
```

### Adding New Instruction Formats

1. Define the field layout in `riscv_encodings.py`
2. Update the instruction database with the new format
3. The parser and generator will automatically handle it
