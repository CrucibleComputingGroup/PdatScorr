#!/bin/bash
# Batch script to compare synthesis results with and without timing constraints
# Tests different ABC depths and generates gate-level results for comparison
# FULLY PARALLEL VERSION - all synthesis jobs run simultaneously

# Don't exit on error when launching background jobs
set +e

# Configuration
DSL_FILE="${1:-../PdatDsl/examples/rv32im.dsl}"
BASE_OUTPUT="${2:-output/comparison}"
ABC_DEPTHS=(2 3 4 5)  # Test different k-induction depths
TIMESTAMP=$(date +%Y%m%d_%H%M%S)

if [ ! -f "$DSL_FILE" ]; then
    echo "ERROR: DSL file '$DSL_FILE' not found"
    echo "Usage: $0 [dsl_file] [output_base_dir]"
    exit 1
fi

DSL_BASENAME=$(basename "$DSL_FILE" .dsl)
OUTPUT_DIR="${BASE_OUTPUT}/${DSL_BASENAME}_${TIMESTAMP}"
SUMMARY_FILE="${OUTPUT_DIR}/summary.txt"
CSV_FILE="${OUTPUT_DIR}/results.csv"
TEMP_DIR="${OUTPUT_DIR}/temp_results"

echo "=========================================="
echo "Batch Synthesis Comparison (PARALLEL)"
echo "=========================================="
echo "DSL file:      $DSL_FILE"
echo "Output dir:    $OUTPUT_DIR"
echo "ABC depths:    ${ABC_DEPTHS[*]}"
echo "Timestamp:     $TIMESTAMP"
echo ""

# Create base output directory first if it doesn't exist
mkdir -p "$(dirname "$OUTPUT_DIR")"

# Create output directories
mkdir -p "$OUTPUT_DIR"
mkdir -p "$TEMP_DIR"

# Create all output subdirectories upfront
for depth in "${ABC_DEPTHS[@]}"; do
    mkdir -p "${OUTPUT_DIR}/isa_only/depth_${depth}"
    mkdir -p "${OUTPUT_DIR}/with_timing/depth_${depth}"
    if [ "$depth" -ge 3 ]; then
        mkdir -p "${OUTPUT_DIR}/isa_only_3stage/depth_${depth}"
        mkdir -p "${OUTPUT_DIR}/with_timing_3stage/depth_${depth}"
    fi
done

# Initialize summary file
cat > "$SUMMARY_FILE" << EOF
========================================
Synthesis Comparison Report (Parallel Run)
========================================
Date: $(date)
DSL: $DSL_FILE
ABC Depths Tested: ${ABC_DEPTHS[*]}

EOF

# Initialize CSV file for easy data analysis
echo "Type,ABC_Depth,Pipeline,Pre_ABC_Gates,Post_ABC_Gates,Gate_Area,Constraints,Time_Seconds,Status" > "$CSV_FILE"

# Function to extract statistics from logs (to be called after synthesis)
extract_stats() {
    local dir="$1"
    local prefix="$2"

    # Extract gate count from AIGER
    local pre_gates=""
    local post_gates=""
    local constraints="0"
    local gate_area=""

    if [ -f "$dir/${prefix}_pre_abc.aig" ]; then
        pre_gates=$(abc -c "read_aiger $dir/${prefix}_pre_abc.aig; ps" 2>&1 | grep "and =" | sed 's/.*and = *//' | sed 's/[^0-9].*//' | head -1)

        # Check for constraints
        local stats=$(abc -c "read_aiger $dir/${prefix}_pre_abc.aig; ps" 2>&1 | grep "i/o")
        if echo "$stats" | grep -q "(c="; then
            constraints=$(echo "$stats" | sed -n 's/.*c=\([0-9]*\).*/\1/p')
        fi
    fi

    if [ -f "$dir/${prefix}_post_abc.aig" ]; then
        post_gates=$(abc -c "read_aiger $dir/${prefix}_post_abc.aig; ps" 2>&1 | grep "and =" | sed 's/.*and = *//' | sed 's/[^0-9].*//' | head -1)
    fi

    # Extract gate area from synthesis log if --gates was used
    if [ -f "$dir/${prefix}_gates.log" ]; then
        gate_area=$(grep "Chip area" "$dir/${prefix}_gates.log" 2>/dev/null | sed 's/.*Chip area for module.*: //' | head -1)
    fi

    echo "$pre_gates|$post_gates|$gate_area|$constraints"
}

# Function to run synthesis (not backgrounded here - will be backgrounded when called)
run_synthesis() {
    local script="$1"
    local abc_depth="$2"
    local output_subdir="$3"
    local type_label="$4"
    local result_file="$5"
    local pipeline="2stage"  # default

    # Determine pipeline configuration
    local extra_args=""
    if [ "$abc_depth" -ge 3 ] && [ "$6" = "3stage" ]; then
        extra_args="--3stage"
        pipeline="3stage"
    fi

    local start_time=$(date +%s)

    echo "[$(date +%H:%M:%S)] Starting: $type_label with ABC depth=$abc_depth" | tee "$output_subdir/timing.log"

    # Run synthesis with --gates flag
    if timeout 600 "$script" --gates --abc-depth "$abc_depth" $extra_args "$DSL_FILE" "$output_subdir" > "$output_subdir/synthesis.log" 2>&1; then
        local end_time=$(date +%s)
        local duration=$((end_time - start_time))

        echo "[$(date +%H:%M:%S)] Completed: $type_label (depth=$abc_depth) in ${duration}s" | tee -a "$output_subdir/timing.log"

        # Extract statistics
        local dsl_base=$(basename "$DSL_FILE" .dsl)
        local dir_suffix=""
        if [[ "$type_label" == *"timing"* ]]; then
            dir_suffix="_timing"
        fi
        local stats=$(extract_stats "$output_subdir/${dsl_base}${dir_suffix}" "ibex_optimized")
        IFS='|' read -r pre_gates post_gates gate_area constraints <<< "$stats"

        # Write results to temp file
        echo "$type_label,$abc_depth,$pipeline,$pre_gates,$post_gates,$gate_area,$constraints,$duration,SUCCESS" > "$result_file"

        # Calculate reduction if possible
        if [ -n "$pre_gates" ] && [ -n "$post_gates" ] && [ "$pre_gates" -gt 0 ]; then
            local reduction=$((100 - (post_gates * 100 / pre_gates)))
            echo "  Reduction: ${reduction}%" | tee -a "$output_subdir/timing.log"
        fi

        return 0
    else
        local end_time=$(date +%s)
        local duration=$((end_time - start_time))
        echo "[$(date +%H:%M:%S)] FAILED: $type_label (depth=$abc_depth) after ${duration}s" | tee -a "$output_subdir/timing.log"
        echo "$type_label,$abc_depth,$pipeline,ERROR,ERROR,ERROR,ERROR,$duration,FAILED" > "$result_file"
        return 1
    fi
}

# Export function and variables for use in subshells
export -f run_synthesis extract_stats
export DSL_FILE OUTPUT_DIR TEMP_DIR

# Main execution
echo "Launching all synthesis runs in parallel..."
echo "This will use significant CPU and memory resources."
echo ""

# Track jobs
JOB_COUNT=0
MAX_JOBS=16  # Maximum parallel jobs

# Launch all synthesis jobs
for depth in "${ABC_DEPTHS[@]}"; do
    # ISA-only version (2-stage)
    if [ -f "./synth_ibex_with_constraints.sh" ]; then
        output_dir="${OUTPUT_DIR}/isa_only/depth_${depth}"
        result_file="${TEMP_DIR}/result_isa_${depth}.csv"
        run_synthesis "./synth_ibex_with_constraints.sh" "$depth" "$output_dir" \
                     "ISA_only" "$result_file" "2stage" &
        ((JOB_COUNT++))
        echo "Launched ISA_only depth=$depth (PID $!)"
    fi

    # ISA+timing version (2-stage)
    if [ -f "./synth_ibex_with_isa_and_timing.sh" ]; then
        output_dir="${OUTPUT_DIR}/with_timing/depth_${depth}"
        result_file="${TEMP_DIR}/result_timing_${depth}.csv"
        run_synthesis "./synth_ibex_with_isa_and_timing.sh" "$depth" "$output_dir" \
                     "ISA+timing" "$result_file" "2stage" &
        ((JOB_COUNT++))
        echo "Launched ISA+timing depth=$depth (PID $!)"
    fi

    # Optional: 3-stage pipeline variants for depth >= 3
    if [ "$depth" -ge 3 ]; then
        if [ -f "./synth_ibex_with_constraints.sh" ]; then
            output_dir="${OUTPUT_DIR}/isa_only_3stage/depth_${depth}"
            result_file="${TEMP_DIR}/result_isa_3s_${depth}.csv"
            run_synthesis "./synth_ibex_with_constraints.sh" "$depth" "$output_dir" \
                         "ISA_only_3stage" "$result_file" "3stage" &
            ((JOB_COUNT++))
            echo "Launched ISA_only_3stage depth=$depth (PID $!)"
        fi

        if [ -f "./synth_ibex_with_isa_and_timing.sh" ]; then
            output_dir="${OUTPUT_DIR}/with_timing_3stage/depth_${depth}"
            result_file="${TEMP_DIR}/result_timing_3s_${depth}.csv"
            run_synthesis "./synth_ibex_with_isa_and_timing.sh" "$depth" "$output_dir" \
                         "ISA+timing_3stage" "$result_file" "3stage" &
            ((JOB_COUNT++))
            echo "Launched ISA+timing_3stage depth=$depth (PID $!)"
        fi
    fi
done

echo ""
echo "Launched $JOB_COUNT parallel synthesis jobs"
echo "Waiting for all jobs to complete..."
echo ""

# Monitor jobs with better progress reporting
while true; do
    RUNNING_JOBS=$(jobs -r | wc -l)
    COMPLETED=$((JOB_COUNT - RUNNING_JOBS))

    echo -ne "\rProgress: $COMPLETED/$JOB_COUNT completed, $RUNNING_JOBS running...     "

    if [ "$RUNNING_JOBS" -eq 0 ]; then
        break
    fi

    sleep 5
done

# Wait for all background jobs to complete
wait

echo -e "\n\nAll synthesis jobs completed!"
echo ""

# Collect all results
echo "Collecting results..."
cat ${TEMP_DIR}/result_*.csv >> "$CSV_FILE" 2>/dev/null || true

# Generate comparison summary
echo "=========================================="
echo "Generating comparison summary..."
echo "=========================================="

# Parse results for summary
declare -A results_isa_only
declare -A results_with_timing

while IFS=',' read -r type depth pipeline pre_gates post_gates gate_area constraints duration status; do
    if [ "$type" != "Type" ] && [ "$status" = "SUCCESS" ]; then
        if [ "$pipeline" = "2stage" ]; then
            if [[ "$type" == "ISA_only" ]]; then
                results_isa_only[$depth]=$post_gates
            elif [[ "$type" == "ISA+timing" ]]; then
                results_with_timing[$depth]=$post_gates
            fi
        fi

        # Add to summary
        cat >> "$SUMMARY_FILE" << EOF

----------------------------------------
$type (ABC depth=$depth, $pipeline)
----------------------------------------
Pre-ABC gates:  $pre_gates
Post-ABC gates: $post_gates
Gate area:      ${gate_area:-N/A}
Constraints:    $constraints
Time:           ${duration}s
EOF

        if [ -n "$pre_gates" ] && [ -n "$post_gates" ] && [ "$pre_gates" -gt 0 ]; then
            reduction=$((100 - (post_gates * 100 / pre_gates)))
            echo "Reduction:      ${reduction}%" >> "$SUMMARY_FILE"
        fi
    fi
done < "$CSV_FILE"

# Add comparison table
cat >> "$SUMMARY_FILE" << EOF

========================================
COMPARISON SUMMARY (2-stage pipeline)
========================================

ABC Depth | ISA Only Gates | ISA+Timing Gates | Difference | % Change
----------------------------------------------------------------------
EOF

for depth in "${ABC_DEPTHS[@]}"; do
    isa_gates="${results_isa_only[$depth]:-N/A}"
    timing_gates="${results_with_timing[$depth]:-N/A}"

    if [ "$isa_gates" != "N/A" ] && [ "$timing_gates" != "N/A" ]; then
        diff=$((timing_gates - isa_gates))
        if [ "$isa_gates" -gt 0 ]; then
            percent=$(( (diff * 100) / isa_gates ))
            printf "%-9s | %-14s | %-16s | %-10s | %+d%%\n" \
                   "$depth" "$isa_gates" "$timing_gates" "$diff" "$percent" >> "$SUMMARY_FILE"
        fi
    else
        printf "%-9s | %-14s | %-16s | N/A        | N/A\n" \
               "$depth" "$isa_gates" "$timing_gates" >> "$SUMMARY_FILE"
    fi
done

# Create visualization script
cat > "${OUTPUT_DIR}/plot_results.py" << 'EOF'
#!/usr/bin/env python3
import csv
import matplotlib.pyplot as plt

# Read CSV file
data = {}
with open('results.csv', 'r') as f:
    reader = csv.DictReader(f)
    for row in reader:
        if row['Status'] == 'SUCCESS' and row['Post_ABC_Gates'] != 'ERROR':
            key = f"{row['Type']}_{row['Pipeline']}"
            if key not in data:
                data[key] = {}
            depth = int(row['ABC_Depth'])
            gates = int(row['Post_ABC_Gates'])
            data[key][depth] = gates

# Plot
fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(15, 6))

# Plot 2-stage pipeline results
depths = sorted(set(sum([list(d.keys()) for d in data.values()], [])))

for key in ['ISA_only_2stage', 'ISA+timing_2stage']:
    if key in data:
        values = [data[key].get(d) for d in depths]
        label = key.replace('_2stage', '').replace('_', ' ')
        ax1.plot(depths, values, 'o-', label=label, linewidth=2, markersize=8)

ax1.set_xlabel('ABC Depth (k-induction)', fontsize=12)
ax1.set_ylabel('Post-ABC Gate Count', fontsize=12)
ax1.set_title('2-Stage Pipeline: ISA vs ISA+Timing', fontsize=14)
ax1.legend(fontsize=11)
ax1.grid(True, alpha=0.3)
ax1.set_xticks(depths)

# Plot 3-stage pipeline results if available
for key in ['ISA_only_3stage', 'ISA+timing_3stage']:
    if key in data:
        values = [data[key].get(d) for d in depths if d >= 3]
        label = key.replace('_3stage', '').replace('_', ' ')
        ax2.plot([d for d in depths if d >= 3], values, 's-', label=label, linewidth=2, markersize=8)

ax2.set_xlabel('ABC Depth (k-induction)', fontsize=12)
ax2.set_ylabel('Post-ABC Gate Count', fontsize=12)
ax2.set_title('3-Stage Pipeline: ISA vs ISA+Timing', fontsize=14)
ax2.legend(fontsize=11)
ax2.grid(True, alpha=0.3)

plt.tight_layout()
plt.savefig('comparison_plot.png', dpi=150)
plt.savefig('comparison_plot.pdf')
print("Plots saved as comparison_plot.png and comparison_plot.pdf")
plt.show()
EOF

chmod +x "${OUTPUT_DIR}/plot_results.py"

# Clean up temp directory
rm -rf "$TEMP_DIR"

# Final summary
echo ""
echo "=========================================="
echo "BATCH SYNTHESIS COMPLETE!"
echo "=========================================="
echo ""
echo "Results saved to: $OUTPUT_DIR"
echo ""
echo "Key files:"
echo "  - summary.txt: Human-readable summary"
echo "  - results.csv: Machine-readable data"
echo "  - plot_results.py: Script to visualize results"
echo ""

# Display summary
tail -25 "$SUMMARY_FILE"

echo ""
echo "To generate plots (requires matplotlib):"
echo "  cd $OUTPUT_DIR && python3 plot_results.py"
echo ""
echo "To monitor CPU/memory usage during parallel runs:"
echo "  htop or top (in another terminal)"