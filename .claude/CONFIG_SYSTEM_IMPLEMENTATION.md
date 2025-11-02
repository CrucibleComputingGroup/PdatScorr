# Config File System Implementation - Architecture & Status

## Overview

This document describes the YAML-based configuration system for PdatScorr synthesis, which replaces hardcoded paths and settings with flexible, validated configuration files.

**Branch:** `config-file-system`

**Status:** Foundation implemented, awaiting review before completing shell script integration

---

## Key Design Decisions

### 1. Multiple Injection Points Architecture

**Problem Addressed:** Your question - "What if injections of different signals are into different modules?"

**Solution:** The schema supports an array of injection points, each with:
- `name`: Unique identifier (e.g., "id_stage_isa", "core_timing")
- `source_file`: Which RTL file to modify (e.g., "rtl/ibex_id_stage.sv")
- `constraint_type`: Type of constraint ("isa", "timing", "custom")
- `module_path`: Hierarchical path for documentation/VCD analysis
- `description`: Human-readable explanation

This allows different constraint types to be injected into different modules simultaneously.

**Example:**
```yaml
injections:
  - name: "id_stage_isa"
    source_file: "rtl/ibex_id_stage.sv"
    constraint_type: "isa"
    module_path: "ibex_core.id_stage_i"

  - name: "core_timing"
    source_file: "rtl/ibex_core.sv"
    constraint_type: "timing"
    module_path: "ibex_core"
```

### 2. Backward Compatibility

**Design:** `make_synthesis_script.py` supports both modes:
- **Legacy mode:** Original command-line interface (no breaking changes)
- **Config mode:** New `--config` flag with YAML file

This ensures existing scripts and tests continue to work while enabling gradual migration.

### 3. Shared Schema with PdatRiscvDsl

**Design:** The config schema extends PdatRiscvDsl's existing schema by adding a `synthesis` section.

**Benefit:** Same config file can be used across both projects.

**Sections:**
- `core_name`, `architecture`, `signals`, `vcd`: From PdatRiscvDsl
- `injections`: New multi-injection design (replaces single `injection`)
- `synthesis`: New section for PdatScorr-specific settings

---

## Implemented Components

### 1. Configuration Schema (`configs/schema.yaml`)

**Location:** `/home/nathan/Projects/PdatProject/PdatScorr/configs/schema.yaml`

**Key Features:**
- JSON Schema format for validation
- Environment variable support (e.g., `$IBEX_ROOT`)
- Multiple injection points
- Synthesis settings (source files, includes, parameters)
- ABC optimization configuration

**Structure:**
```yaml
synthesis:
  core_root: "$IBEX_ROOT"              # Supports env vars
  top_module: "ibex_core"
  include_dirs: [...]                  # Relative to core_root
  source_files: [...]                  # In dependency order
  parameters:
    writeback_stage: false
  abc:
    default_depth: 2
```

### 2. Config Loader (`scripts/config_loader.py`)

**Location:** `/home/nathan/Projects/PdatProject/PdatScorr/scripts/config_loader.py`

**Features:**
- YAML parsing with validation
- Environment variable expansion (`$VAR` and `${VAR}`)
- Automatic fallback paths for core_root
- Type-safe dataclasses (InjectionPoint, SynthesisConfig, CoreConfig)
- Helpful error messages

**Key Classes:**
```python
@dataclass
class InjectionPoint:
    name: str
    source_file: str
    constraint_type: str
    module_path: Optional[str]
    description: Optional[str]

@dataclass
class CoreConfig:
    core_name: str
    synthesis: SynthesisConfig
    injections: List[InjectionPoint]
    # ... other fields

    def get_injection(self, constraint_type: str) -> Optional[InjectionPoint]
    def get_injection_by_name(self, name: str) -> Optional[InjectionPoint]
```

**Usage:**
```python
from config_loader import ConfigLoader

config = ConfigLoader.load_config("configs/ibex.yaml")
print(config.synthesis.core_root_resolved)  # Absolute path
```

### 3. Updated Synthesis Script Generator (`scripts/make_synthesis_script.py`)

**Location:** `/home/nathan/Projects/PdatProject/PdatScorr/scripts/make_synthesis_script.py`

**Modes:**

**Legacy Mode (unchanged):**
```bash
python3 scripts/make_synthesis_script.py \
    path/to/modified_id_stage.sv \
    -o synth.ys \
    -a output_base \
    --ibex-root /path/to/ibex \
    --writeback-stage \
    --core-modified path/to/modified_core.sv
```

**Config Mode (new):**
```bash
python3 scripts/make_synthesis_script.py \
    --config configs/ibex.yaml \
    --modified-files id_stage_isa=/path/to/modified_id.sv \
                     core_timing=/path/to/modified_core.sv \
    -o synth.ys \
    -a output_base
```

**Key Functions:**
- `generate_synthesis_script()`: Legacy mode (preserved)
- `generate_synthesis_script_from_config()`: Config mode (new)
- `_generate_synthesis_commands()`: Shared synthesis logic

**Smart File Replacement:**
The config mode automatically:
1. Reads source file list from config
2. Identifies which files are injection targets
3. Replaces them with modified versions from `--modified-files`
4. Uses original files for non-injected modules

### 4. Example Configuration (`configs/ibex.yaml`)

**Location:** `/home/nathan/Projects/PdatProject/PdatScorr/configs/ibex.yaml`

**Contains:**
- Full Ibex configuration
- 2 injection points (id_stage_isa, core_timing)
- Complete source file list (23 files)
- All include directories
- Default parameters

---

## Tested Functionality

✅ **Config Loading:**
```bash
$ python3 scripts/config_loader.py configs/ibex.yaml --dump
✓ Successfully loaded config: ibex
  Architecture: rv32
  Core root: /home/nathan/Projects/PdatProject/PdatCoreSim/cores/ibex
  Top module: ibex_core
  Source files: 23 files
  Injection points: 2
    - id_stage_isa: isa → rtl/ibex_id_stage.sv
    - core_timing: timing → rtl/ibex_core.sv
```

✅ **Config-Based Script Generation:**
```bash
$ python3 scripts/make_synthesis_script.py \
    --config configs/ibex.yaml \
    --modified-files id_stage_isa=/tmp/test_id.sv core_timing=/tmp/test_core.sv \
    -o /tmp/test_synth.ys

Generated synthesis script (config mode): /tmp/test_synth.ys
  Config:      configs/ibex.yaml
  Core:        ibex
  Injections:  2 modified files
```

✅ **Correct File Replacement:**
- Verifies `ibex_id_stage.sv` replaced with `/tmp/test_id.sv`
- Verifies `ibex_core.sv` replaced with `/tmp/test_core.sv`
- Verifies all other files use original paths

---

## Remaining Work

### Phase 1: Shell Script Integration

#### 1.1 Update `synth_ibex_with_constraints.sh`

**Current Interface:**
```bash
./synth_ibex_with_constraints.sh [OPTIONS] <rules.dsl> [output_dir]
```

**Proposed Interface:**
```bash
./synth_ibex_with_constraints.sh [OPTIONS] <rules.dsl> [output_dir]

New Options:
  --config FILE         Use config file instead of hardcoded paths
  --core NAME           Core name (default: ibex, looks for configs/NAME.yaml)
```

**Changes Needed:**
1. Add config file argument parsing
2. If `--config` provided:
   - Load config with Python config_loader
   - Pass config path to `make_synthesis_script.py` via `--config`
   - Pass modified file paths via `--modified-files`
3. Otherwise: Use legacy mode (current behavior)

**Implementation Strategy:**
```bash
if [ -n "$CONFIG_FILE" ]; then
    # Config mode
    python3 scripts/make_synthesis_script.py \
        --config "$CONFIG_FILE" \
        --modified-files "id_stage_isa=${ID_STAGE_SV}" \
                         "core_timing=${CORE_SV}" \
        -o "$SYNTH_SCRIPT" \
        -a "${BASE}"
else
    # Legacy mode (current implementation)
    python3 scripts/make_synthesis_script.py \
        "$ID_STAGE_SV" \
        -o "$SYNTH_SCRIPT" \
        -a "${BASE}" \
        --ibex-root "$IBEX_ROOT" \
        $CORE_MODIFIED_FLAG
fi
```

#### 1.2 Update `batch_synth.sh`

**Changes:**
- Add `--config` flag to pass through to `synth_ibex_with_constraints.sh`
- Maintain backward compatibility

### Phase 2: Testing Updates

#### 2.1 Create Fixture Configs

**Create:** `tests/regression/fixtures/ibex_test.yaml`
- Minimal config for testing
- Same content as `configs/ibex.yaml` but in fixtures directory

#### 2.2 Update `test_ibex_synthesis.py`

**Changes:**
1. Add config mode tests alongside existing tests
2. New test class: `TestConfigMode`
   - Test with config file
   - Test config validation errors
   - Test missing config file handling
3. Maintain existing tests (verify backward compatibility)

**Example Test:**
```python
def test_synthesis_with_config(self, temp_output_dir):
    """Test synthesis using config file."""
    dsl_file = FIXTURES_DIR / "baseline.dsl"
    config_file = FIXTURES_DIR / "ibex_test.yaml"

    result = run_synthesis(
        dsl_file,
        temp_output_dir,
        extra_args=["--config", str(config_file)]
    )

    assert result.success
    assert "Config mode" in result.stdout or result.has_file("ibex_optimized_yosys.aig")
```

#### 2.3 Add Config Validation Tests

**New File:** `tests/regression/test_config_validation.py`

**Tests:**
- Invalid YAML syntax
- Missing required fields
- Invalid core_root path
- Invalid injection configuration
- Schema validation

### Phase 3: Documentation

#### 3.1 Config README (`configs/README.md`)

**Contents:**
- Overview of config system
- Schema description
- How to create a new config for a different core
- Environment variable usage
- Migration guide from hardcoded paths

#### 3.2 Update Main README

**Add Section:**
- "Configuration System" overview
- Link to `configs/README.md`
- Quick start with config files

---

## Migration Strategy

### For Existing Users

**No Breaking Changes:**
- All existing scripts work unchanged
- Legacy mode maintained indefinitely
- Gradual migration path

**Migration Steps:**
1. Start using `--config` flag in new work
2. Gradually update existing scripts
3. Eventually deprecate legacy mode (future decision)

### For New Cores (e.g., BOOM, Rocket)

**Process:**
1. Copy `configs/ibex.yaml` → `configs/newcore.yaml`
2. Update paths, source files, injection points
3. Test with `python3 scripts/config_loader.py configs/newcore.yaml`
4. Use `--config configs/newcore.yaml` in synthesis scripts

---

## Design Rationale

### Why YAML?

- **Human-readable:** Easy to edit without programming knowledge
- **Standard:** JSON Schema validation support
- **Flexible:** Supports comments, anchors, multi-line strings
- **Compatible:** PdatRiscvDsl already uses YAML

### Why Multiple Injections?

Your question highlighted a real architectural need:
- ISA constraints → ID stage
- Timing constraints → Core top-level
- Future: Memory constraints → LSU
- Future: Branch predictor constraints → Branch unit

Single injection point was limiting.

### Why Backward Compatibility?

- Don't break existing CI/CD
- Don't invalidate existing documentation
- Allow gradual migration
- Reduce review/testing burden

---

## Files Created/Modified

### Created:
```
configs/
├── schema.yaml                    # JSON schema for validation
└── ibex.yaml                      # Example Ibex configuration

scripts/
└── config_loader.py               # Configuration loading library

.claude/
└── CONFIG_SYSTEM_IMPLEMENTATION.md  # This document
```

### Modified:
```
scripts/
└── make_synthesis_script.py       # Added config mode support
```

### To Be Modified:
```
synth_ibex_with_constraints.sh     # Shell script integration
batch_synth.sh                     # Pass-through config flag
tests/regression/test_ibex_synthesis.py  # Add config tests
```

---

## Questions for Review

1. **Schema Design:** Does the multi-injection architecture meet your needs? Any additional injection scenarios to consider?

2. **Interface:** Is the `--config` + `--modified-files` interface intuitive for the shell script integration?

3. **Backward Compatibility:** Should we maintain legacy mode indefinitely, or plan deprecation?

4. **Testing:** Should we test both modes for every scenario, or focus new tests on config mode?

5. **Environment Variables:** Should we support additional fallback mechanisms beyond `$IBEX_ROOT`?

6. **Scope:** Should this PR also include configs for other cores (BOOM, Rocket), or just Ibex as a template?

---

## Next Steps (Pending Your Review)

**If approved:**
1. Complete shell script integration (Phase 1)
2. Update regression tests (Phase 2)
3. Write documentation (Phase 3)
4. Run full regression suite
5. Create pull request

**If changes needed:**
- Revise based on feedback
- Re-test affected components
- Update documentation

---

## Testing the Current Implementation

**Load and validate config:**
```bash
python3 scripts/config_loader.py configs/ibex.yaml --dump
```

**Generate synthesis script in config mode:**
```bash
python3 scripts/make_synthesis_script.py \
    --config configs/ibex.yaml \
    --modified-files id_stage_isa=/tmp/test_id.sv \
    -o /tmp/test.ys \
    -a /tmp/output
```

**Verify legacy mode still works:**
```bash
python3 scripts/make_synthesis_script.py \
    /path/to/id_stage.sv \
    -o /tmp/legacy.ys \
    -a /tmp/output
```
