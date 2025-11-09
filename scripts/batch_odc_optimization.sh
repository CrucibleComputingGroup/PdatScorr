#!/bin/bash
# Batch two-pass ODC optimization
# Runs ODC analysis + optimization on multiple DSL files

set -e

if [ "$#" -lt 1 ]; then
    echo "Usage: $0 [OPTIONS] <dsl_files_or_dirs...>"
    echo ""
    echo "Run two-pass ODC optimization on multiple DSL files"
    echo ""
    echo "Options: Same as batch_synth.sh"
    echo ""
    echo "Example:"
    echo "  $0 --config configs/ibex.yaml examples/shifts/*.dsl"
    exit 0
fi

# Collect all DSL files
DSL_FILES=()
for arg in "$@"; do
    if [ -f "$arg" ] && [[ "$arg" == *.dsl ]]; then
        DSL_FILES+=("$arg")
    elif [ -d "$arg" ]; then
        while IFS= read -r -d '' file; do
            DSL_FILES+=("$file")
        done < <(find "$arg" -maxdepth 1 -name "*.dsl" -print0)
    fi
done

if [ ${#DSL_FILES[@]} -eq 0 ]; then
    echo "ERROR: No DSL files found"
    exit 1
fi

echo "=========================================="
echo "Batch ODC Optimization (Two-Pass)"
echo "=========================================="
echo "DSL files: ${#DSL_FILES[@]}"
echo ""

# Summary arrays
declare -A BASELINE_GATES
declare -A OPTIMIZED_GATES
declare -A REDUCTIONS

# Process each DSL file
for i in "${!DSL_FILES[@]}"; do
    DSL="${DSL_FILES[$i]}"
    DSL_NAME=$(basename "$DSL" .dsl)
    
    echo ""
    echo "[$((i+1))/${#DSL_FILES[@]}] Processing: $DSL_NAME"
    echo "=========================================="
    
    # Run two-pass optimization
    ./scripts/synth_with_odc_optimization.sh --config configs/ibex.yaml "$DSL"
    
    if [ $? -eq 0 ]; then
        # Extract stats
        BASELINE_AIG="output/${DSL_NAME}/ibex_optimized_post_abc.aig"
        OPTIMIZED_AIG="output/${DSL_NAME}/odc_optimized_synthesis/ibex_alu_optimized_post_abc.aig"
        
        if [ -f "$BASELINE_AIG" ]; then
            BASELINE_GATES[$DSL_NAME]=$(abc -c "read_aiger $BASELINE_AIG; print_stats" 2>&1 | grep -oP 'and\s*=\s*\K\d+')
        fi
        
        if [ -f "$OPTIMIZED_AIG" ]; then
            OPTIMIZED_GATES[$DSL_NAME]=$(abc -c "read_aiger $OPTIMIZED_AIG; print_stats" 2>&1 | grep -oP 'and\s*=\s*\K\d+')
            
            if [ -n "${BASELINE_GATES[$DSL_NAME]}" ] && [ -n "${OPTIMIZED_GATES[$DSL_NAME]}" ]; then
                REDUCTION=$((BASELINE_GATES[$DSL_NAME] - OPTIMIZED_GATES[$DSL_NAME]))
                REDUCTIONS[$DSL_NAME]=$REDUCTION
            fi
        fi
    fi
done

# Print summary table
echo ""
echo "=========================================="
echo "ODC Optimization Summary"
echo "=========================================="
printf "%-20s %12s %12s %12s %10s\n" "DSL" "Baseline" "Optimized" "Reduction" "Percent"
echo "--------------------------------------------------------------------------------"

for DSL_NAME in "${!BASELINE_GATES[@]}"; do
    BASE=${BASELINE_GATES[$DSL_NAME]}
    OPT=${OPTIMIZED_GATES[$DSL_NAME]:-N/A}
    RED=${REDUCTIONS[$DSL_NAME]:-0}
    
    if [ "$OPT" != "N/A" ] && [ -n "$BASE" ]; then
        PCT=$(python3 -c "print(f'{100.0 * $RED / $BASE:.2f}%')")
        printf "%-20s %12s %12s %12s %10s\n" "$DSL_NAME" "$BASE" "$OPT" "$RED" "$PCT"
    else
        printf "%-20s %12s %12s %12s %10s\n" "$DSL_NAME" "$BASE" "$OPT" "-" "-"
    fi
done

echo ""
echo "Reports available in:"
echo "  output/<dsl_name>/odc_analysis/odc_report.md"

