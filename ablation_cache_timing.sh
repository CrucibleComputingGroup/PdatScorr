#!/bin/bash
# Ablation Study: Post-Cone Optimization Strategies for Cache Timing Constraints
# Tests which post-processing best removes constraint hardware overhead
# Creates clearly-named test files for easy cleanup

set -e

# ========================================
# Configuration
# ========================================
DSL_FILE="${1:-../PdatDsl/examples/rv32im.dsl}"
BASE_OUTPUT="${2:-output/ablation_$(date +%Y%m%d_%H%M%S)}"

# ABC depths to test
ABC_DEPTHS=(2 4 6 8)

# Test configurations - different post-cone optimization strategies
declare -A CONFIGS
CONFIGS=(
    ["baseline"]="cone -O 0 -R \$REAL_OUTPUTS; print_stats"
    ["configA_blif_cone"]="write_blif TMP.blif; read_blif TMP.blif; cone -O 0 -R \$REAL_OUTPUTS; print_stats"
    ["configB_cone_fraig"]="cone -O 0 -R \$REAL_OUTPUTS; fraig; print_stats"
    ["configC_cone_dc2"]="cone -O 0 -R \$REAL_OUTPUTS; dc2; print_stats"
    ["configD_cone_dretime"]="cone -O 0 -R \$REAL_OUTPUTS; dretime; print_stats"
    ["configE_cone_fraig_dc2"]="cone -O 0 -R \$REAL_OUTPUTS; fraig; dc2; print_stats"
    ["configF_cone_fraig_dc2_dretime"]="cone -O 0 -R \$REAL_OUTPUTS; fraig; dc2; dretime; print_stats"
    ["configG_blif_cone_fraig_dc2_dretime"]="write_blif TMP.blif; read_blif TMP.blif; cone -O 0 -R \$REAL_OUTPUTS; fraig; dc2; dretime; print_stats"
    ["configH_cone_strash_fraig_dc2"]="cone -O 0 -R \$REAL_OUTPUTS; strash; fraig; dc2; print_stats"
)

# ========================================
# Validation
# ========================================
if [ ! -f "$DSL_FILE" ]; then
    echo "ERROR: DSL file '$DSL_FILE' not found"
    exit 1
fi

if [ ! -f "./synth_ibex_with_constraints.sh" ]; then
    echo "ERROR: synth_ibex_with_constraints.sh not found"
    exit 1
fi

if [ ! -f "./synth_ibex_with_cache_timing.sh" ]; then
    echo "ERROR: synth_ibex_with_cache_timing.sh not found"
    exit 1
fi

DSL_BASENAME=$(basename "$DSL_FILE" .dsl)
RESULTS_CSV="${BASE_OUTPUT}/ablation_results.csv"
SUMMARY_TXT="${BASE_OUTPUT}/ablation_summary.txt"

echo "=========================================="
echo "Ablation Study: Cache Timing Post-Cone Optimization"
echo "=========================================="
echo "DSL file:       $DSL_FILE"
echo "Output dir:     $BASE_OUTPUT"
echo "ABC depths:     ${ABC_DEPTHS[*]}"
echo "Configurations: ${#CONFIGS[@]}"
echo ""

# Create output directory
mkdir -p "$BASE_OUTPUT"

# Initialize CSV
echo "Configuration,ABC_Depth,Constraint_Type,PreABC_Gates,PostABC_Gates,Constraint_Cones,Chip_Area_um2,Status" > "$RESULTS_CSV"

# ========================================
# Helper Function: Create Modified Cache Timing Script
# ========================================
create_config_script() {
    local config_name="$1"
    local cone_command="$2"
    local output_script="${BASE_OUTPUT}/ablation_${config_name}.sh"

    # Copy base script and modify the cone extraction line
    cp ./synth_ibex_with_cache_timing.sh "$output_script"

    # Replace the cone extraction command
    sed -i "s|cone -O 0 -R \$REAL_OUTPUTS; trim; strash; print_stats|${cone_command}|g" "$output_script"

    chmod +x "$output_script"
    echo "$output_script"
}

# ========================================
# Generate Test Scripts for Each Configuration
# ========================================
echo "Generating test scripts for each configuration..."
declare -A CONFIG_SCRIPTS

for config_name in "${!CONFIGS[@]}"; do
    cone_cmd="${CONFIGS[$config_name]}"
    script_path=$(create_config_script "$config_name" "$cone_cmd")
    CONFIG_SCRIPTS["$config_name"]="$script_path"
    echo "  Created: $script_path"
done

echo ""

# ========================================
# Create All Output Directories Upfront
# ========================================
echo "Creating output directories..."

# ISA baseline directories
for depth in "${ABC_DEPTHS[@]}"; do
    mkdir -p "${BASE_OUTPUT}/isa_baseline/depth_${depth}"
done

# All configuration directories
for config in "${!CONFIGS[@]}"; do
    for depth in "${ABC_DEPTHS[@]}"; do
        mkdir -p "${BASE_OUTPUT}/${config}/depth_${depth}"
    done
done

echo "Directories created"
echo ""

# ========================================
# Run Baseline (ISA-only) Tests
# ========================================
echo "=========================================="
echo "Running ISA-Only Baseline Tests"
echo "=========================================="

declare -a baseline_pids=()

for depth in "${ABC_DEPTHS[@]}"; do
    output_dir="${BASE_OUTPUT}/isa_baseline/depth_${depth}"
    echo "Launching ISA-only baseline (depth=$depth)..."
    ./synth_ibex_with_constraints.sh --gates --abc-depth "$depth" "$DSL_FILE" "$output_dir" \
        > "$output_dir/synthesis.log" 2>&1 &
    baseline_pids+=($!)
done

echo "Launched ${#baseline_pids[@]} baseline jobs"
echo ""

# ========================================
# Run Configuration Tests (All Configs × All Depths)
# ========================================
echo "=========================================="
echo "Running Ablation Study Configurations"
echo "=========================================="

declare -a test_pids=()
declare -a test_labels=()

for config in "${!CONFIGS[@]}"; do
    script="${CONFIG_SCRIPTS[$config]}"

    for depth in "${ABC_DEPTHS[@]}"; do
        output_dir="${BASE_OUTPUT}/${config}/depth_${depth}"
        echo "Launching ${config} (depth=$depth)..."

        "$script" --gates --abc-depth "$depth" "$DSL_FILE" "$output_dir" \
            > "$output_dir/synthesis.log" 2>&1 &

        test_pids+=($!)
        test_labels+=("${config}_d${depth}")
    done
done

total_jobs=$((${#baseline_pids[@]} + ${#test_pids[@]}))
echo ""
echo "Launched ${#test_pids[@]} configuration test jobs"
echo "Total jobs running: $total_jobs"
echo "Waiting for all jobs to complete..."
echo ""

# ========================================
# Monitor Progress
# ========================================
while true; do
    running=$(jobs -r | wc -l)
    completed=$((total_jobs - running))

    echo -ne "\rProgress: $completed/$total_jobs completed, $running running...     "

    if [ "$running" -eq 0 ]; then
        break
    fi

    sleep 10
done

wait

echo -e "\n\nAll jobs completed!"
echo ""

# ========================================
# Collect Results
# ========================================
echo "=========================================="
echo "Collecting Results"
echo "=========================================="

# Function to extract metrics from logs
extract_metrics() {
    local output_dir="$1"
    local dsl_base="$2"
    local config_type="$3"

    local abc_log="${output_dir}/${dsl_base}/ibex_optimized_abc.log"
    local gates_log="${output_dir}/${dsl_base}/ibex_optimized_gates.log"

    # Default values
    local pre_gates="N/A"
    local post_gates="N/A"
    local constraint_cones="N/A"
    local chip_area="N/A"
    local status="FAILED"

    if [ -f "$abc_log" ]; then
        # Extract pre-ABC gates
        pre_gates=$(grep "and =" "$abc_log" | head -1 | sed 's/.*and = *//' | sed 's/[^0-9].*//')

        # Extract post-ABC gates (after cone extraction)
        post_gates=$(grep "and =" "$abc_log" | tail -1 | sed 's/.*and = *//' | sed 's/[^0-9].*//')

        # Extract constraint cones
        if grep -q "Constraint cones" "$abc_log"; then
            constraint_cones=$(grep "Constraint cones" "$abc_log" | sed -n 's/.*Constraint cones = *\([0-9]*\).*/\1/p')
        fi

        # Check if succeeded
        if [ -f "${output_dir}/${dsl_base}/ibex_optimized_post_abc.aig" ]; then
            status="SUCCESS"
        fi
    fi

    # Extract chip area if gates synthesis succeeded
    if [ -f "$gates_log" ]; then
        chip_area=$(grep "Chip area for module" "$gates_log" 2>/dev/null | tail -1 | sed 's/.*: //' | sed 's/ µm²//' | sed 's/,//g')
    fi

    echo "$pre_gates|$post_gates|$constraint_cones|$chip_area|$status"
}

# Collect baseline results
echo "Collecting baseline (ISA-only) results..."
for depth in "${ABC_DEPTHS[@]}"; do
    output_dir="${BASE_OUTPUT}/isa_baseline/depth_${depth}"
    metrics=$(extract_metrics "$output_dir" "$DSL_BASENAME" "isa_only")
    IFS='|' read -r pre post cones area status <<< "$metrics"

    echo "baseline,$depth,ISA_only,$pre,$post,$cones,$area,$status" >> "$RESULTS_CSV"
done

# Collect configuration test results
echo "Collecting configuration test results..."
for config in "${!CONFIGS[@]}"; do
    for depth in "${ABC_DEPTHS[@]}"; do
        output_dir="${BASE_OUTPUT}/${config}/depth_${depth}"

        # Determine constraint type based on config
        if [[ "$config" == "baseline" ]]; then
            dsl_suffix=""
        else
            dsl_suffix="_cache"
        fi

        metrics=$(extract_metrics "$output_dir" "${DSL_BASENAME}${dsl_suffix}" "cache_timing")
        IFS='|' read -r pre post cones area status <<< "$metrics"

        echo "$config,$depth,cache_timing,$pre,$post,$cones,$area,$status" >> "$RESULTS_CSV"
    done
done

echo "Results collected!"
echo ""

# ========================================
# Generate Summary Report
# ========================================
echo "=========================================="
echo "Generating Summary Report"
echo "=========================================="

cat > "$SUMMARY_TXT" << EOF
========================================
Ablation Study: Cache Timing Post-Cone Optimization
========================================
Date: $(date)
DSL: $DSL_FILE
ABC Depths Tested: ${ABC_DEPTHS[*]}
Configurations Tested: ${#CONFIGS[@]}

========================================
Test Configurations
========================================

baseline: cone only (no post-processing)
configA:  write_blif → read_blif → cone
configB:  cone → fraig
configC:  cone → dc2
configD:  cone → dretime
configE:  cone → fraig → dc2
configF:  cone → fraig → dc2 → dretime
configG:  write_blif → read_blif → cone → fraig → dc2 → dretime
configH:  cone → strash → fraig → dc2

========================================
Results Summary (Chip Area in µm²)
========================================

EOF

# Create comparison table
echo "" >> "$SUMMARY_TXT"
echo "Configuration Comparison (ABC Depth 4):" >> "$SUMMARY_TXT"
echo "----------------------------------------" >> "$SUMMARY_TXT"

# Show depth 4 results as primary comparison
depth=4
baseline_area=$(grep "^baseline,$depth" "$RESULTS_CSV" | cut -d',' -f7)

echo "" >> "$SUMMARY_TXT"
printf "%-35s %15s %15s %15s\n" "Configuration" "Chip Area (µm²)" "vs Baseline" "Status" >> "$SUMMARY_TXT"
echo "----------------------------------------------------------------------------------------------------" >> "$SUMMARY_TXT"
printf "%-35s %15s %15s %15s\n" "ISA-only baseline" "$baseline_area" "0 (baseline)" "Reference" >> "$SUMMARY_TXT"

for config in baseline configA_blif_cone configB_cone_fraig configC_cone_dc2 configD_cone_dretime configE_cone_fraig_dc2 configF_cone_fraig_dc2_dretime configG_blif_cone_fraig_dc2_dretime configH_cone_strash_fraig_dc2; do
    line=$(grep "^${config},$depth" "$RESULTS_CSV" 2>/dev/null)
    if [ -n "$line" ]; then
        area=$(echo "$line" | cut -d',' -f7)
        status=$(echo "$line" | cut -d',' -f8)

        if [ "$area" != "N/A" ] && [ "$baseline_area" != "N/A" ]; then
            diff=$(echo "$area - $baseline_area" | bc)
            printf "%-35s %15s %+15.2f %15s\n" "$config" "$area" "$diff" "$status" >> "$SUMMARY_TXT"
        else
            printf "%-35s %15s %15s %15s\n" "$config" "$area" "N/A" "$status" >> "$SUMMARY_TXT"
        fi
    fi
done

# Add detailed results per depth
echo "" >> "$SUMMARY_TXT"
echo "========================================" >> "$SUMMARY_TXT"
echo "Detailed Results by Depth" >> "$SUMMARY_TXT"
echo "========================================" >> "$SUMMARY_TXT"

for depth in "${ABC_DEPTHS[@]}"; do
    echo "" >> "$SUMMARY_TXT"
    echo "ABC Depth $depth:" >> "$SUMMARY_TXT"
    echo "----------------------------------------" >> "$SUMMARY_TXT"

    baseline_area=$(grep "^baseline,$depth" "$RESULTS_CSV" | cut -d',' -f7)

    for config in baseline configA_blif_cone configB_cone_fraig configC_cone_dc2 configD_cone_dretime configE_cone_fraig_dc2 configF_cone_fraig_dc2_dretime configG_blif_cone_fraig_dc2_dretime configH_cone_strash_fraig_dc2; do
        line=$(grep "^${config},$depth" "$RESULTS_CSV" 2>/dev/null)
        if [ -n "$line" ]; then
            area=$(echo "$line" | cut -d',' -f7)
            cones=$(echo "$line" | cut -d',' -f6)
            printf "  %-35s: %12s µm² (constraint cones: %s)\n" "$config" "$area" "$cones" >> "$SUMMARY_TXT"
        fi
    done
done

# ========================================
# Final Output
# ========================================
echo ""
echo "=========================================="
echo "Ablation Study Complete!"
echo "=========================================="
echo ""
echo "Results saved to:"
echo "  - $RESULTS_CSV (machine-readable)"
echo "  - $SUMMARY_TXT (human-readable)"
echo ""
echo "Output directory structure:"
echo "  $BASE_OUTPUT/"
echo "    ├── isa_baseline/           # ISA-only reference"
echo "    ├── baseline/                # Cache timing, cone only"
echo "    ├── configA_blif_cone/"
echo "    ├── configB_cone_fraig/"
echo "    ├── ... (other configs)"
echo "    ├── ablation_*.sh            # Generated test scripts"
echo "    ├── ablation_results.csv"
echo "    └── ablation_summary.txt"
echo ""
echo "To view summary:"
echo "  cat $SUMMARY_TXT"
echo ""
echo "To remove all ablation files:"
echo "  rm -rf $BASE_OUTPUT"
echo "  rm -f ${BASE_OUTPUT%/*}/ablation_*.sh"
echo ""

# Display key findings
tail -30 "$SUMMARY_TXT"
