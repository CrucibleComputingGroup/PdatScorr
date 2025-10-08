#!/bin/bash
# Run external ABC for sequential optimization on BLIF file
#
# Usage: ./run_external_abc.sh <input.blif> <output.blif>

set -e

if [ "$#" -ne 2 ]; then
    echo "Usage: $0 <input.blif> <output.blif>"
    echo ""
    echo "Runs ABC sequential optimization (scorr) on a BLIF file"
    exit 1
fi

INPUT_BLIF="$1"
OUTPUT_BLIF="$2"

if [ ! -f "$INPUT_BLIF" ]; then
    echo "ERROR: Input file '$INPUT_BLIF' not found"
    exit 1
fi

echo "=========================================="
echo "External ABC Sequential Optimization"
echo "=========================================="
echo "Input:  $INPUT_BLIF"
echo "Output: $OUTPUT_BLIF"
echo ""

# Check if ABC is available
if ! command -v abc &> /dev/null; then
    echo "ERROR: 'abc' command not found"
    echo "Please install ABC: https://github.com/berkeley-abc/abc"
    exit 1
fi

echo "Running ABC with sequential optimization (scorr)..."
echo ""

# Run ABC with sequential optimization script
abc -c "read_blif $INPUT_BLIF; \
        print_stats; \
        strash; \
        print_stats; \
        scorr; \
        print_stats; \
        dc2; \
        print_stats; \
        dretime; \
        print_stats; \
        write_blif $OUTPUT_BLIF"

if [ $? -eq 0 ]; then
    echo ""
    echo "=========================================="
    echo "SUCCESS!"
    echo "=========================================="
    echo "Optimized BLIF written to: $OUTPUT_BLIF"
else
    echo "ERROR: ABC optimization failed"
    exit 1
fi
