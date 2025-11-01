#!/bin/bash
# Regression test runner for Ibex synthesis
#
# Usage: ./run_regression.sh [pytest-options]
#
# Examples:
#   ./run_regression.sh                    # Run all tests in parallel
#   ./run_regression.sh -v                 # Verbose output
#   ./run_regression.sh -k test_baseline   # Run specific test
#   ./run_regression.sh -m "not slow"      # Skip slow tests (faster)
#   ./run_regression.sh -n 4               # Override parallelism (default: auto)

set -e

# Get script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

echo "========================================"
echo "Ibex Synthesis Regression Tests"
echo "========================================"
echo "Project root: $PROJECT_ROOT"
echo ""

# Check dependencies
echo "Checking dependencies..."

# Check for pytest
if ! command -v pytest &> /dev/null; then
    echo "ERROR: pytest not found"
    echo "Install with: pip install pytest"
    exit 1
fi

# Check for synlig
if ! command -v synlig &> /dev/null; then
    echo "WARNING: synlig not found - tests will fail"
    echo "Install from: https://github.com/chipsalliance/synlig"
fi

# Check for ABC (optional but recommended)
if ! command -v abc &> /dev/null; then
    echo "WARNING: abc not found - some test checks will be skipped"
    echo "Install from: https://github.com/berkeley-abc/abc"
fi

# Check for pdat-dsl
if ! command -v pdat-dsl &> /dev/null; then
    echo "ERROR: pdat-dsl not found"
    echo "Install with: pip install -r requirements.txt"
    exit 1
fi

# Check for Ibex core
if [ -z "$IBEX_ROOT" ]; then
    if [ -d "$PROJECT_ROOT/../PdatCoreSim/cores/ibex" ]; then
        export IBEX_ROOT="$PROJECT_ROOT/../PdatCoreSim/cores/ibex"
    elif [ -d "$PROJECT_ROOT/../CoreSim/cores/ibex" ]; then
        export IBEX_ROOT="$PROJECT_ROOT/../CoreSim/cores/ibex"
    else
        echo "ERROR: Could not find Ibex core"
        echo "Set IBEX_ROOT environment variable or place Ibex in:"
        echo "  - ../PdatCoreSim/cores/ibex"
        echo "  - ../CoreSim/cores/ibex"
        exit 1
    fi
fi

echo "Using Ibex core: $IBEX_ROOT"
echo ""

# Run pytest
echo "Running tests..."
echo ""

cd "$SCRIPT_DIR/regression"

# Default options if none provided
if [ $# -eq 0 ]; then
    pytest -n auto -v
else
    pytest -n auto "$@"
fi

exit_code=$?

echo ""
if [ $exit_code -eq 0 ]; then
    echo "========================================"
    echo "All tests passed!"
    echo "========================================"
else
    echo "========================================"
    echo "Some tests failed (exit code: $exit_code)"
    echo "========================================"
fi

exit $exit_code
