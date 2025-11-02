# Regression Test Design for Ibex Synthesis

## Overview
Regression tests to ensure the synthesis flow completes successfully and generates all expected output files.

## Test Scope
- **Focus**: Synthesis flow completion, not optimization quality
- **Target**: Ibex core synthesis with constraints
- **Key Checks**:
  - All steps complete without errors
  - Expected output files are generated
  - Files have non-zero size
  - Log files indicate success

## Expected Output Files (per synthesis)

From analyzing `synth_ibex_with_constraints.sh`, expected outputs:

### Core Outputs (always generated)
1. `*_assumptions.sv` - Generated ISA assumptions
2. `*_id_stage.sv` - Modified ibex_id_stage with injected assumptions
3. `*_synth.ys` - Yosys synthesis script
4. `*_yosys.aig` - AIGER from Yosys (pre-ABC)
5. `*_yosys.log` - Yosys synthesis log

### Optional Timing Files (when timing constraints present)
6. `*_assumptions_timing.sv` - Timing constraint code
7. `*_core.sv` - Modified ibex_core with timing

### ABC Optimization Outputs (when abc available)
8. `*_post_abc.aig` - Optimized AIGER after ABC scorr
9. `*_abc.log` - ABC optimization log

### Gate-level Outputs (with --gates flag)
10. `*_gates.v` - Gate-level netlist
11. `*_gates.log` - Gate synthesis log
12. `*_gate_synth.ys` - Gate-level synthesis script

## Test Fixtures

### Test DSL Files
1. **baseline.dsl** - Minimal RV32I baseline
2. **rv32im.dsl** - Full RV32IM (if available)
3. **simple_outlawed.dsl** - Small ISA constraint set

## Test Cases

### TC1: Basic ISA-Only Synthesis
- Input: baseline.dsl
- Command: `./synth_ibex_with_constraints.sh <dsl>`
- Expected: Core outputs (1-5) + ABC outputs (8-9)
- Checks:
  - Exit code 0
  - All expected files exist
  - Log shows "SUCCESS!"
  - AIGER files non-empty

### TC2: 3-Stage Pipeline
- Input: baseline.dsl
- Command: `./synth_ibex_with_constraints.sh --3stage <dsl>`
- Expected: Same as TC1
- Additional checks:
  - Log shows "Enabling 3-stage pipeline"

### TC3: Custom ABC Depth
- Input: baseline.dsl
- Command: `./synth_ibex_with_constraints.sh --abc-depth 4 <dsl>`
- Expected: Same as TC1
- Additional checks:
  - Log shows "ABC k-induction depth: 4"

### TC4: Gate-level Synthesis
- Input: baseline.dsl
- Command: `./synth_ibex_with_constraints.sh --gates <dsl>`
- Expected: Core + ABC + Gate outputs (10-12)
- Checks:
  - Gate-level netlist exists
  - Area reported in log

## Implementation Strategy

### Test Framework (Python-based)
```
tests/
├── regression/
│   ├── test_ibex_synthesis.py    # Main test suite
│   ├── fixtures/
│   │   ├── baseline.dsl          # Test DSL files
│   │   ├── simple_outlawed.dsl
│   │   └── README.md
│   ├── conftest.py               # Pytest configuration
│   └── utils.py                  # Helper functions
└── run_regression.sh             # Test runner script
```

### Test Implementation
- Framework: pytest
- Isolation: Each test runs in temporary directory
- Cleanup: Configurable (keep outputs on failure)
- Parallelization: pytest-xdist for parallel execution

### Assertions
1. **Exit code**: Process exits with 0
2. **File existence**: All expected files created
3. **File size**: Non-zero size (basic sanity)
4. **Log parsing**: Success messages present
5. **Error detection**: No ERROR messages in logs
6. **AIGER validity**: Basic header check

## Future Enhancements
1. Compare gate counts across runs (detect regressions)
2. Parse ABC logs for optimization statistics
3. Timing constraint validation
4. Integration with CI/CD
5. Performance benchmarking
