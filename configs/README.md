# PDAT Synthesis Configuration Files

This directory contains YAML configuration files that specify how to synthesize different RISC-V cores with instruction constraints.

## Overview

The configuration system replaces hardcoded paths and settings with flexible, validated YAML files. This enables:

- **Multi-core support**: Same scripts work with Ibex, BOOM, Rocket, CVA6, etc.
- **Multiple injection points**: Different constraints can be injected into different modules
- **Environment flexibility**: Environment variables and fallback paths supported
- **Validation**: Configs are validated against a schema with helpful error messages
- **Backward compatibility**: Legacy mode still works without configs

## Quick Start

### Using Config Files

```bash
# Synthesize with config file
./synth_ibex_with_constraints.sh --config configs/ibex.yaml my_rules.dsl

# Auto-load config by core name
./synth_ibex_with_constraints.sh --core ibex my_rules.dsl

# Batch synthesis with config
./batch_synth.sh --config configs/ibex.yaml rules/*.dsl
```

### Legacy Mode (Still Supported)

```bash
# Works exactly as before - no config needed
./synth_ibex_with_constraints.sh my_rules.dsl
```

## Configuration File Structure

### Top-Level Fields

```yaml
core_name: "ibex"          # Core identifier
architecture: "rv32"       # RV32 or RV64

# Signal mappings (from PdatRiscvDsl)
signals:
  instruction_data: "instr_rdata_i"
  pc: "pc_if_o"
  operands:
    alu:
      rs1: "alu_operand_a_ex_i"
      rs2: "alu_operand_b_ex_i"

# Multiple injection points (NEW)
injections:
  - name: "id_stage_isa"
    source_file: "rtl/ibex_id_stage.sv"
    constraint_type: "isa"
    description: "ISA constraints in ID stage"

  - name: "core_timing"
    source_file: "rtl/ibex_core.sv"
    constraint_type: "timing"
    description: "Cache timing constraints"

# Synthesis settings (NEW)
synthesis:
  core_root: "$IBEX_ROOT"      # Supports env vars
  top_module: "ibex_core"
  include_dirs: [...]
  source_files: [...]
  parameters:
    writeback_stage: false
  abc:
    default_depth: 2

# VCD analysis (from PdatRiscvDsl)
vcd:
  testbench_prefix: "tb_ibex_random.dut"
```

### Injection Points

The `injections` section supports multiple injection points, enabling different constraint types to be injected into different modules:

```yaml
injections:
  # ISA constraints → ID stage
  - name: "id_stage_isa"
    source_file: "rtl/ibex_id_stage.sv"
    constraint_type: "isa"
    module_path: "ibex_core.id_stage_i"
    description: "Instruction encoding constraints"

  # Timing constraints → Core
  - name: "core_timing"
    source_file: "rtl/ibex_core.sv"
    constraint_type: "timing"
    module_path: "ibex_core"
    description: "Cache timing assumptions"

  # Custom constraints → LSU (example)
  - name: "lsu_memory"
    source_file: "rtl/ibex_load_store_unit.sv"
    constraint_type: "custom"
    module_path: "ibex_core.load_store_unit_i"
    description: "Memory access constraints"
```

**Fields:**
- `name`: Unique identifier (used in `--modified-files`)
- `source_file`: RTL file to modify (relative to `core_root`)
- `constraint_type`: Type of constraint (`isa`, `timing`, `custom`)
- `module_path`: Hierarchical path (optional, for documentation)
- `description`: Human-readable explanation

### Synthesis Settings

```yaml
synthesis:
  # Core location (supports environment variables)
  core_root: "$IBEX_ROOT"
  # Fallbacks: ../PdatCoreSim/cores/ibex, ../CoreSim/cores/ibex

  # Top-level module
  top_module: "ibex_core"

  # Include directories (relative to core_root)
  include_dirs:
    - "rtl"
    - "shared/rtl"
    - "vendor/lowrisc_ip/ip/prim/rtl"

  # Source files in dependency order
  source_files:
    - "rtl/ibex_pkg.sv"
    - "rtl/ibex_alu.sv"
    - "rtl/ibex_id_stage.sv"    # Will be replaced if injected
    - "rtl/ibex_core.sv"         # Will be replaced if injected

  # Synthesis parameters
  parameters:
    writeback_stage: false       # 2-stage vs 3-stage pipeline
    # Add core-specific parameters here

  # ABC optimization settings
  abc:
    default_depth: 2             # k-induction depth
```

## Environment Variables

Config files support environment variable expansion:

```yaml
# Dollar sign syntax
core_root: "$IBEX_ROOT"
core_root: "$IBEX_ROOT/subdir"

# Braces syntax
core_root: "${IBEX_ROOT}"
core_root: "${IBEX_ROOT}/subdir"
```

**Fallback Behavior:**
If an environment variable is not set, the loader will try common fallback paths:
- `../PdatCoreSim/cores/ibex`
- `../CoreSim/cores/ibex`

## Creating a Config for a New Core

1. **Copy Template:**
   ```bash
   cp configs/ibex.yaml configs/newcore.yaml
   ```

2. **Update Core Information:**
   ```yaml
   core_name: "boom"
   architecture: "rv64"
   ```

3. **Update Signal Mappings:**
   Find signal names in the core's RTL and update:
   ```yaml
   signals:
     instruction_data: "core_inst"  # Core-specific name
     pc: "core_pc"
     operands:
       alu:
         rs1: "alu_rs1_data"
         rs2: "alu_rs2_data"
   ```

4. **Configure Injection Points:**
   Identify where to inject constraints:
   ```yaml
   injections:
     - name: "decode_isa"
       source_file: "rtl/boom_decode.sv"
       constraint_type: "isa"
   ```

5. **Set Synthesis Paths:**
   ```yaml
   synthesis:
     core_root: "$BOOM_ROOT"
     source_files:
       - "rtl/boom_pkg.sv"
       - "rtl/boom_decode.sv"
       # ... all source files in order
   ```

6. **Test Configuration:**
   ```bash
   python3 scripts/config_loader.py configs/newcore.yaml --dump
   ```

7. **Test Synthesis:**
   ```bash
   ./synth_ibex_with_constraints.sh --config configs/newcore.yaml test.dsl
   ```

## Validation

Configs are validated against `configs/schema.yaml` (JSON Schema format).

**Common Validation Errors:**

```
Missing required fields in config: architecture
```
→ Add missing top-level field

```
Missing required fields in synthesis: source_files
```
→ Add required synthesis section field

```
Core root directory not found: /bad/path
```
→ Fix path or set environment variable

```
Config file not found: configs/foo.yaml
```
→ Check filename spelling

## Testing Your Config

### Validate Config
```bash
python3 scripts/config_loader.py configs/yourcore.yaml --dump
```

### Test Synthesis
```bash
# Quick test with minimal DSL
./synth_ibex_with_constraints.sh --config configs/yourcore.yaml \
    tests/regression/fixtures/baseline.dsl /tmp/test_output
```

### Run Tests
```bash
# Test config loading
pytest tests/regression/test_config_validation.py -v

# Test synthesis
pytest tests/regression/test_ibex_synthesis.py::TestConfigMode -v
```

## Files

- `schema.yaml`: JSON Schema for validation
- `ibex.yaml`: Ibex core configuration (reference implementation)
- `README.md`: This file

## Advanced Usage

### Override Parameters

Parameters in the config can be overridden by command-line flags:

```bash
# Config has writeback_stage: false
# Override to 3-stage mode
./synth_ibex_with_constraints.sh --config configs/ibex.yaml --3stage rules.dsl
```

### Custom ABC Depth

```bash
./synth_ibex_with_constraints.sh --config configs/ibex.yaml --abc-depth 4 rules.dsl
```

### Batch Synthesis

```bash
# Synthesize all DSL files with same config
./batch_synth.sh --config configs/ibex.yaml --gates -j 8 rules/*.dsl
```

## Migration from Legacy Mode

**Old (hardcoded):**
```bash
export IBEX_ROOT=/path/to/ibex
./synth_ibex_with_constraints.sh my_rules.dsl
```

**New (config-based):**
```bash
# Option 1: Use environment variable (no change needed)
./synth_ibex_with_constraints.sh --config configs/ibex.yaml my_rules.dsl

# Option 2: Set path in config file
# Edit configs/ibex.yaml: core_root: "/path/to/ibex"
./synth_ibex_with_constraints.sh --config configs/ibex.yaml my_rules.dsl

# Option 3: Auto-load by core name
./synth_ibex_with_constraints.sh --core ibex my_rules.dsl
```

**Advantages:**
- No hardcoded paths in scripts
- Easy to switch between cores
- Configuration is versioned with code
- Multiple injection points supported
- Validated against schema

## Troubleshooting

### "Config file not found"
Check that the file exists:
```bash
ls -la configs/
```

### "Core root directory not found"
Set the environment variable:
```bash
export IBEX_ROOT=/path/to/ibex
```
Or update the config file with an absolute path.

### "Missing required fields"
Run validation to see what's missing:
```bash
python3 scripts/config_loader.py configs/yourconfig.yaml
```

### "Module not found: yaml"
Install PyYAML:
```bash
pip install pyyaml
```

## See Also

- PdatRiscvDsl configs: `../PdatRiscvDsl/configs/`
- Schema documentation: `schema.yaml`
- Test configs: `../tests/regression/fixtures/`
- Implementation notes: `../.claude/CONFIG_SYSTEM_IMPLEMENTATION.md`
