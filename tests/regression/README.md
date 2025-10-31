# Ibex Synthesis Regression Tests

Automated regression tests to ensure the Ibex synthesis flow completes successfully and generates all expected output files.

## Overview

These tests focus on **synthesis flow completion**, not optimization quality. They verify that:
- All synthesis steps complete without errors
- Expected output files are generated
- Files have valid content (non-zero size, correct format)
- Log files indicate success

## Quick Start

```bash
# From project root
cd tests
./run_regression.sh

# Or with pytest directly
cd tests/regression
pytest -v
```

## Test Structure

```
tests/
├── regression/
│   ├── test_ibex_synthesis.py    # Main test suite
│   ├── fixtures/                 # Test input files
│   │   ├── baseline.dsl
│   │   └── simple_outlawed.dsl
│   ├── conftest.py               # Pytest configuration
│   ├── utils.py                  # Helper functions
│   └── README.md                 # This file
└── run_regression.sh             # Test runner script
```

## Test Coverage

### Test Files

1. **test_ibex_synthesis.py** (8 tests)
   - Basic synthesis flow
   - Command-line options
   - Error handling
   - Output organization
   - Log validation

2. **test_batch_synth.py** (12 tests)
   - Batch synthesis with multiple files
   - Parallel execution
   - Multiple runs per DSL
   - Directory input
   - Output organization

### Test Classes (test_ibex_synthesis.py)

1. **TestBasicSynthesis**
   - `test_baseline_dsl`: Minimal RV32I baseline
   - `test_instruction_constraints`: DSL with instruction constraints

2. **TestSynthesisOptions**
   - `test_3stage_pipeline`: Tests `--3stage` flag
   - `test_custom_abc_depth`: Tests `--abc-depth N` parameter

3. **TestErrorHandling**
   - `test_missing_dsl_file`: Graceful failure on missing inputs
   - `test_invalid_abc_depth`: Validation of parameters

4. **TestOutputOrganization**
   - `test_output_subdirectory_creation`: Verify file organization

5. **TestLogParsing**
   - `test_no_errors_in_yosys_log`: Parse logs for errors

### Test Classes (test_batch_synth.py)

1. **TestBasicBatchSynthesis**
   - `test_single_file`: Single DSL file processing
   - `test_multiple_files`: Multiple DSL files in parallel
   - `test_directory_input`: Directory scanning

2. **TestBatchOptions**
   - `test_parallel_jobs`: `-j/--jobs` option
   - `test_extra_synthesis_args`: Passing args to synthesis script
   - `test_multiple_runs`: `--runs` option for multiple runs

3. **TestBatchErrorHandling**
   - `test_no_dsl_files`: No input files provided
   - `test_nonexistent_file`: Non-existent file handling

4. **TestBatchOutputOrganization**
   - `test_output_directory_structure`: File organization
   - `test_multiple_runs_organization`: Multi-run structure

5. **TestBatchLogging**
   - `test_synthesis_logs_created`: Log file generation
   - `test_batch_status_messages`: Status reporting

### Expected Outputs

Each test verifies the following files are generated:

**Core outputs (always):**
- `*_assumptions.sv` - Generated ISA assumptions
- `*_id_stage.sv` - Modified ibex_id_stage.sv
- `*_synth.ys` - Yosys synthesis script
- `*_yosys.aig` - AIGER from Yosys
- `*_yosys.log` - Synthesis log

**ABC optimization (when abc available):**
- `*_post_abc.aig` - Optimized AIGER
- `*_abc.log` - ABC log

**Gate-level (with --gates flag):**
- `*_gates.v` - Gate-level netlist
- `*_gates.log` - Gate synthesis log
- `*_gate_synth.ys` - Gate synthesis script

## Running Tests

### Basic Usage

```bash
# Run all tests
./run_regression.sh

# Verbose output
./run_regression.sh -v

# Run specific test
./run_regression.sh -k test_baseline_dsl

# Show test names without running
./run_regression.sh --collect-only
```

### Advanced Usage

```bash
# Skip slow tests
./run_regression.sh -m "not slow"

# Run tests in parallel (requires pytest-xdist)
./run_regression.sh -n auto

# Stop on first failure
./run_regression.sh -x

# Show local variables on failure
./run_regression.sh -l

# Generate HTML report (requires pytest-html)
./run_regression.sh --html=report.html
```

### Filtering Tests

```bash
# Run only basic synthesis tests
pytest -k "TestBasicSynthesis"

# Run only error handling tests
pytest -k "TestErrorHandling"

# Run tests matching pattern
pytest -k "baseline or outlawed"
```

## Requirements

### Essential
- Python 3.7+
- pytest
- pdat-dsl (from requirements.txt)
- synlig (SystemVerilog frontend)
- Ibex core (auto-detected from ../PdatCoreSim or ../CoreSim)

### Optional
- abc (for sequential optimization tests)
- pytest-xdist (for parallel test execution)
- pytest-html (for HTML reports)

### Installation

```bash
# Install Python dependencies
pip install pytest pytest-xdist pytest-html

# Or from project requirements
pip install -r ../requirements.txt

# Install system tools (varies by platform)
# - synlig: https://github.com/chipsalliance/synlig
# - abc: https://github.com/berkeley-abc/abc
```

## Environment Variables

- `IBEX_ROOT`: Path to Ibex core (auto-detected if not set)

## Adding New Tests

1. **Add test fixture**: Place new `.dsl` file in `fixtures/`

2. **Add test method**: In appropriate test class in `test_ibex_synthesis.py`

```python
def test_my_new_case(self, temp_output_dir):
    """Test description."""
    dsl_file = FIXTURES_DIR / "my_test.dsl"
    result = run_synthesis(dsl_file, temp_output_dir)

    assert result.success
    assert result.has_file("expected_output.aig")
    # Add more assertions...
```

3. **Run the test**:
```bash
./run_regression.sh -k test_my_new_case
```

## Troubleshooting

### Tests fail with "synlig not found"
Install synlig or ensure it's in your PATH.

### Tests fail with "Could not find Ibex core"
Set `IBEX_ROOT` environment variable:
```bash
export IBEX_ROOT=/path/to/ibex
./run_regression.sh
```

### Some tests are skipped
Tests requiring ABC will run but skip certain checks if `abc` is not installed. This is expected behavior.

### Test output is too verbose
Use pytest's output control:
```bash
./run_regression.sh -q           # Quiet mode
./run_regression.sh --tb=short   # Shorter tracebacks
```

### Want to keep test outputs for debugging
Test outputs are in temporary directories (automatically cleaned up). To inspect:
```bash
# Run with pytest directly and check tmp_path location
pytest -v -s
# Outputs will be in /tmp/pytest-* directories
```

Or modify the test to use a fixed output directory for debugging.

## Continuous Integration

Example GitHub Actions workflow:

```yaml
name: Regression Tests

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - name: Set up Python
        uses: actions/setup-python@v4
        with:
          python-version: '3.10'
      - name: Install dependencies
        run: |
          pip install -r requirements.txt
          pip install pytest pytest-xdist
      - name: Install synlig
        run: |
          # Add synlig installation steps
      - name: Run regression tests
        run: |
          cd tests
          ./run_regression.sh -v
```

## Future Enhancements

Potential improvements to the test suite:

1. **Quality metrics**: Compare gate counts, area across runs
2. **Performance tracking**: Detect synthesis time regressions
3. **ABC statistics**: Parse and validate optimization statistics
4. **Timing constraints**: Add tests for timing constraint injection
5. **Gate-level tests**: Expand coverage for `--gates` option
6. **Multi-run stability**: Test non-determinism handling
7. **Equivalence checking**: Verify logical equivalence of outputs

## License

Same license as parent project.
