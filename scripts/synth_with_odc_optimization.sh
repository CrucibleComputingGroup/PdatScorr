#!/bin/bash
# Two-pass synthesis with ODC optimization
# 
# Pass 1: Synthesize + ODC analysis
# Pass 2: Apply ODC tie-offs + re-synthesize + compare

set -e

if [ "$#" -lt 1 ]; then
    echo "Usage: $0 [SYNTH_OPTIONS] <rules.dsl>"
    echo ""
    echo "Two-pass synthesis with ODC optimization:"
    echo "  1. Synthesize + run ODC analysis"
    echo "  2. Apply ODC tie-offs + re-synthesize"  
    echo "  3. Compare baseline vs optimized area"
    echo ""
    echo "Example:"
    echo "  $0 --config configs/ibex.yaml examples/shifts/slli2.dsl"
    exit 0
fi

# Get DSL file (last argument)
for last; do true; done
DSL_FILE="$last"
DSL_BASENAME=$(basename "$DSL_FILE" .dsl)

echo "=========================================="
echo "Two-Pass ODC Optimization Workflow"
echo "=========================================="
echo "DSL: $DSL_FILE"
echo ""

# Pass 1: Baseline synthesis + ODC analysis
echo "[Pass 1/2] Baseline synthesis + ODC analysis..."
./synth_ibex_with_constraints.sh --odc-analysis "$@"

if [ $? -ne 0 ]; then
    echo "ERROR: Baseline synthesis failed"
    exit 1
fi

# Find the output directory
BASELINE_DIR="output/${DSL_BASENAME}"
ODC_REPORT="$BASELINE_DIR/odc_analysis/odc_report.json"

if [ ! -f "$ODC_REPORT" ]; then
    echo "ERROR: ODC report not found at: $ODC_REPORT"
    exit 1
fi

# Check ODC count
ODC_COUNT=$(python3 -c "
import json
with open('$ODC_REPORT') as f:
    report = json.load(f)
print(report['metadata']['confirmed_odcs'])
")

if [ "$ODC_COUNT" -eq 0 ]; then
    echo ""
    echo "=========================================="
    echo "No ODCs found - baseline is already optimal"
    echo "=========================================="
    exit 0
fi

echo ""
echo "[Pass 2/2] Applying $ODC_COUNT ODC optimizations and re-synthesizing..."
echo "=========================================="

# Determine core RTL directory  
if [ -n "$IBEX_ROOT" ]; then
    CORE_RTL="$IBEX_ROOT/rtl"
elif [ -d "../PdatCoreSim/cores/ibex/rtl" ]; then
    CORE_RTL="../PdatCoreSim/cores/ibex/rtl"
else
    echo "ERROR: Could not find Ibex RTL"
    exit 1
fi

# Create optimized RTL
OPTIMIZED_RTL_DIR="$BASELINE_DIR/odc_optimized_rtl"
mkdir -p "$OPTIMIZED_RTL_DIR"

python3 scripts/apply_odc_optimizations.py "$ODC_REPORT" \
    --rtl-dir "$CORE_RTL" \
    --output-dir "$OPTIMIZED_RTL_DIR"

if [ $? -ne 0 ]; then
    echo "ERROR: Failed to generate optimized RTL"
    exit 1
fi

# Synthesize optimized version
OPTIMIZED_OUTPUT="$BASELINE_DIR/odc_optimized_synthesis"
mkdir -p "$OPTIMIZED_OUTPUT"

# IMPORTANT: Copy optimized ALU to synthesis output directory
# so it can be found by Synlig (which uses basename)
cp "$OPTIMIZED_RTL_DIR/ibex_alu_optimized.sv" "$OPTIMIZED_OUTPUT/"

echo ""
echo "Re-synthesizing with ODC-optimized RTL..."

# Use Python to call synthesis
python3 << PYEOF
import sys
from pathlib import Path
sys.path.insert(0, 'odc')
from synthesis import synthesize_error_injected_circuit

result = synthesize_error_injected_circuit(
    error_injected_rtl=Path('$OPTIMIZED_OUTPUT/ibex_alu_optimized.sv'),
    dsl_file=Path('$DSL_FILE'),
    output_dir=Path('$OPTIMIZED_OUTPUT'),
    config_file=Path('configs/ibex.yaml'),
    k_depth=2
)

if result:
    print(f'Optimized synthesis complete')
    sys.exit(0)
else:
    print('ERROR: Synthesis failed')
    sys.exit(1)
PYEOF

if [ $? -ne 0 ]; then
    echo "ERROR: Optimized synthesis failed"
    exit 1
fi

# Run ABC optimization
OPTIMIZED_YOSYS_AIG="$OPTIMIZED_OUTPUT/ibex_alu_optimized_yosys.aig"
OPTIMIZED_ABC_AIG="$OPTIMIZED_OUTPUT/ibex_alu_optimized_post_abc.aig"

echo ""
echo "Running ABC optimization on ODC-optimized circuit..."

# Use same ABC optimization as baseline (scorr + constraint removal + additional opts)
# First check if there are constraints to remove
ABC_STATS_OPT=$(abc -c "read_aiger $OPTIMIZED_YOSYS_AIG; print_stats" 2>&1 | grep "i/o")

if echo "$ABC_STATS_OPT" | grep -q "(c="; then
    # Has constraints - remove them after scorr
    TOTAL_OUTPUTS=$(echo "$ABC_STATS_OPT" | grep -oP 'i/o\s*=\s*\d+/\s*\K\d+')
    CONSTR_COUNT=$(echo "$ABC_STATS_OPT" | grep -oP '\(c=\K\d+')
    REAL_OUTPUTS=$((TOTAL_OUTPUTS - CONSTR_COUNT))

    # Build constraint removal commands
    CONSTRAINT_CMDS="constr -r;"
    for ((i=TOTAL_OUTPUTS-1; i>=REAL_OUTPUTS; i--)); do
        CONSTRAINT_CMDS="$CONSTRAINT_CMDS removepo -N $i;"
    done
else
    CONSTRAINT_CMDS=""
fi

abc -c "
    read_aiger $OPTIMIZED_YOSYS_AIG;
    strash;
    cycle 100;
    scorr -c -m -F 2 -C 30000 -S 20 -v;
    $CONSTRAINT_CMDS
    rewrite -l;
    fraig;
    balance -l;
    print_stats;
    write_aiger $OPTIMIZED_ABC_AIG;
" > "$OPTIMIZED_OUTPUT/abc.log" 2>&1

# Compare results
echo ""
echo "=========================================="
echo "ODC Optimization Results"
echo "=========================================="

BASELINE_STATS=$(abc -c "read_aiger $BASELINE_DIR/ibex_optimized_post_abc.aig; print_stats" 2>&1 | grep "i/o =")
OPTIMIZED_STATS=$(abc -c "read_aiger $OPTIMIZED_ABC_AIG; print_stats" 2>&1 | grep "i/o =")

echo "Baseline:  $BASELINE_STATS"
echo "Optimized: $OPTIMIZED_STATS"
echo ""

# Extract AND gate counts
BASELINE_AND=$(echo "$BASELINE_STATS" | grep -oP 'and\s*=\s*\K\d+')
OPTIMIZED_AND=$(echo "$OPTIMIZED_STATS" | grep -oP 'and\s*=\s*\K\d+')

if [ -n "$BASELINE_AND" ] && [ -n "$OPTIMIZED_AND" ]; then
    REDUCTION=$((BASELINE_AND - OPTIMIZED_AND))
    PERCENT=$(python3 -c "print(f'{100.0 * $REDUCTION / $BASELINE_AND:.2f}')")

    echo "AND gate reduction: $REDUCTION gates ($PERCENT%)"
    echo ""

    if [ "$REDUCTION" -gt 0 ]; then
        echo "✓ ODC optimization achieved area reduction!"
    else
        echo "⚠ No area reduction (ABC may have already optimized these signals)"
    fi
fi

echo ""
echo "Output files:"
echo "  Baseline synthesis: $BASELINE_DIR/"
echo "  ODC report:         $ODC_REPORT"
echo "  Optimized RTL:      $OPTIMIZED_RTL_DIR/"
echo "  Optimized synthesis: $OPTIMIZED_OUTPUT/"
