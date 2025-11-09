#!/bin/bash
# Batch synthesis script - run multiple DSL files in parallel
# Usage: ./batch_synth.sh [OPTIONS] <dsl1> <dsl2> ...

set -e

# Default values
MAX_PARALLEL=4
BASE_OUTPUT_DIR="output"
EXTRA_ARGS=""
USE_GNU_PARALLEL=false
VERBOSE=false
RUNS_PER_DSL=1

# Color codes for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Parse command line arguments
while [[ "$#" -gt 0 ]]; do
    case $1 in
        -j|--jobs)
            MAX_PARALLEL="$2"
            shift 2
            ;;
        -o|--output-dir|--output)
            BASE_OUTPUT_DIR="$2"
            shift 2
            ;;
        --gates)
            EXTRA_ARGS="$EXTRA_ARGS --gates"
            shift
            ;;
        --3stage)
            EXTRA_ARGS="$EXTRA_ARGS --3stage"
            shift
            ;;
        --abc-depth)
            EXTRA_ARGS="$EXTRA_ARGS --abc-depth $2"
            shift 2
            ;;
        --config)
            EXTRA_ARGS="$EXTRA_ARGS --config $2"
            shift 2
            ;;
        --core)
            EXTRA_ARGS="$EXTRA_ARGS --core $2"
            shift 2
            ;;
        --odc-analysis)
            EXTRA_ARGS="$EXTRA_ARGS --odc-analysis"
            shift
            ;;
        --gnu-parallel)
            USE_GNU_PARALLEL=true
            shift
            ;;
        --runs)
            RUNS_PER_DSL="$2"
            shift 2
            ;;
        -v|--verbose)
            VERBOSE=true
            shift
            ;;
        -h|--help)
            echo "Usage: $0 [OPTIONS] <files_or_dirs>..."
            echo ""
            echo "Run multiple DSL synthesis jobs in parallel"
            echo ""
            echo "Options:"
            echo "  -j, --jobs N              Maximum parallel jobs (default: 4)"
            echo "  -o, --output-dir, --output DIR  Base output directory (default: output)"
            echo "  --runs N              Number of runs per DSL file (default: 1)"
            echo "  --gates               Pass --gates to synthesis script"
            echo "  --3stage              Pass --3stage to synthesis script"
            echo "  --abc-depth N         Pass --abc-depth N to synthesis script"
            echo "  --config FILE         Pass --config FILE to synthesis script (config mode)"
            echo "  --core NAME           Pass --core NAME to synthesis script (auto-config)"
            echo "  --odc-analysis        Run ODC analysis after synthesis for each DSL"
            echo "  --gnu-parallel        Use GNU parallel if available (faster)"
            echo "  -v, --verbose         Show detailed output from each job"
            echo "  -h, --help            Show this help message"
            echo ""
            echo "Arguments:"
            echo "  Can be DSL files, directories containing DSL files, or wildcards"
            echo ""
            echo "Examples:"
            echo "  $0 ../PdatDsl/examples/           # Process all DSL files in directory"
            echo "  $0 -j 8 dir1/ dir2/ file.dsl     # Mix directories and files"
            echo "  $0 --gates -j 4 ../PdatDsl/examples/  # All files with gates"
            echo "  $0 rules/*.dsl                    # Wildcard expansion"
            echo "  $0 -j 8 test1.dsl test2.dsl      # Specific files"
            echo "  $0 --config configs/ibex.yaml rules/*.dsl  # Use config file"
            echo "  $0 --odc-analysis -j 8 rules/*.dsl  # Run ODC analysis on all files"
            echo ""
            echo "Each DSL file will be processed to its own subfolder:"
            echo "  test.dsl → output/test/"
            exit 0
            ;;
        *)
            break
            ;;
    esac
done

# Process remaining arguments - can be DSL files or directories
RAW_ARGS=("$@")
DSL_FILES=()

# Expand directories to DSL files
for arg in "${RAW_ARGS[@]}"; do
    if [ -d "$arg" ]; then
        # It's a directory - find all .dsl files in it
        echo "Scanning directory: $arg"
        while IFS= read -r -d '' file; do
            DSL_FILES+=("$file")
        done < <(find "$arg" -maxdepth 1 -name "*.dsl" -type f -print0 | sort -z)

        # Report what we found
        num_found=$(find "$arg" -maxdepth 1 -name "*.dsl" -type f | wc -l)
        echo "  Found $num_found DSL files in $arg"
    elif [ -f "$arg" ]; then
        # It's a file - add it directly
        DSL_FILES+=("$arg")
    else
        echo -e "${YELLOW}Warning: '$arg' is not a file or directory, skipping${NC}"
    fi
done

if [ ${#DSL_FILES[@]} -eq 0 ]; then
    echo -e "${RED}Error: No DSL files found${NC}"
    echo "Run with -h for help"
    exit 1
fi

# Check if synthesis script exists
if [ ! -f "./synth_core.sh" ]; then
    echo -e "${RED}Error: synth_core.sh not found in current directory${NC}"
    exit 1
fi

# Check if GNU parallel is available and requested
if [ "$USE_GNU_PARALLEL" = true ] && command -v parallel &> /dev/null; then
    echo -e "${GREEN}Using GNU parallel for job management${NC}"
    USE_GNU_PARALLEL=true
else
    USE_GNU_PARALLEL=false
fi

echo "=========================================="
echo "Batch Synthesis Configuration"
echo "=========================================="
echo "DSL files:        ${#DSL_FILES[@]} files"
echo "Runs per DSL:     $RUNS_PER_DSL"
echo "Max parallel:     $MAX_PARALLEL"
echo "Output directory: $BASE_OUTPUT_DIR"
echo "Extra arguments:  $EXTRA_ARGS"
echo ""

# Create output directory
mkdir -p "$BASE_OUTPUT_DIR"

# Function to run a single synthesis job
run_synthesis() {
    local dsl_file="$1"
    local job_num="$2"
    local total_jobs="$3"
    local run_num="${4:-1}"  # Default to run 1 if not specified

    # Get base name for status display
    local dsl_basename=$(basename "$dsl_file" .dsl)

    # Determine output directory based on whether we have multiple runs
    if [ "$RUNS_PER_DSL" -gt 1 ]; then
        # Pass parent directory - synth script will create dsl_basename subdirectory
        local parent_dir="$BASE_OUTPUT_DIR/run_${run_num}"
        local actual_output_dir="${parent_dir}/${dsl_basename}"
        local display_name="${dsl_basename} (run ${run_num})"
    else
        local parent_dir="$BASE_OUTPUT_DIR"
        local actual_output_dir="$BASE_OUTPUT_DIR/${dsl_basename}"
        local display_name="${dsl_basename}"
    fi

    # Determine log file location (will be created by synth script)
    local log_file="${actual_output_dir}/synthesis.log"

    # Create parent and actual output directories
    mkdir -p "${actual_output_dir}"

    # Print start message
    echo -e "${BLUE}[$job_num/$total_jobs] Starting: ${display_name}${NC}"

    # Run synthesis
    local start_time=$(date +%s)

    if [ "$VERBOSE" = true ]; then
        # Show output directly
        ./synth_core.sh $EXTRA_ARGS "$dsl_file" "$parent_dir" 2>&1 | tee "$log_file"
        local exit_code=${PIPESTATUS[0]}
    else
        # Redirect to log file
        ./synth_core.sh $EXTRA_ARGS "$dsl_file" "$parent_dir" > "$log_file" 2>&1
        local exit_code=$?
    fi

    local end_time=$(date +%s)
    local duration=$((end_time - start_time))

    # Print completion message
    if [ $exit_code -eq 0 ]; then
        echo -e "${GREEN}[$job_num/$total_jobs] ✓ Completed: ${display_name} (${duration}s)${NC}"
        # Show key metrics if available
        if [ -f "$actual_output_dir/ibex_optimized_abc.log" ]; then
            local stats=$(grep "and =" "$actual_output_dir/ibex_optimized_abc.log" | tail -1)
            if [ ! -z "$stats" ]; then
                echo "  └─ Final: $stats"
            fi
        fi
        # Store area if available for later comparison
        if [ -f "$actual_output_dir/synthesis.log" ]; then
            grep "Chip area:" "$actual_output_dir/synthesis.log" | tail -1 | sed -n 's/.*Chip area: *\([0-9.]*\).*/\1/p' > "$actual_output_dir/area.txt" 2>/dev/null || true
        fi
    else
        echo -e "${RED}[$job_num/$total_jobs] ✗ Failed: ${display_name} (${duration}s)${NC}"
        echo "  └─ Check log: $log_file"
    fi

    return $exit_code
}

# Function to select the best run for a given DSL
select_best_run() {
    local dsl_basename="$1"
    local best_area=999999999999
    local best_run=""
    local best_and_gates=999999999

    # Only needed if we have multiple runs
    if [ "$RUNS_PER_DSL" -eq 1 ]; then
        return 0
    fi

    # Find run with minimum area (or AND gates if area not available)
    # New structure: output/run_N/dsl_name/
    for run_num in $(seq 1 $RUNS_PER_DSL); do
        local run_dir="$BASE_OUTPUT_DIR/run_${run_num}/${dsl_basename}"

        if [ ! -d "$run_dir" ]; then
            continue
        fi

        # First try to get chip area
        if [ -f "$run_dir/area.txt" ] && [ -s "$run_dir/area.txt" ]; then
            local area=$(cat "$run_dir/area.txt")
            if [ ! -z "$area" ] && (( $(echo "$area < $best_area" | bc -l 2>/dev/null || echo 0) )); then
                best_area=$area
                best_run="run_${run_num}"
            fi
        elif [ -f "$run_dir/ibex_optimized_abc.log" ]; then
            # Fall back to AND gate count if no area
            local and_gates=$(grep "and =" "$run_dir/ibex_optimized_abc.log" | tail -1 | sed -n 's/.*and = *\([0-9]*\).*/\1/p')
            if [ ! -z "$and_gates" ] && [ "$and_gates" -lt "$best_and_gates" ]; then
                best_and_gates=$and_gates
                best_run="run_${run_num}"
                best_area=$and_gates  # For display
            fi
        fi
    done

    # Create symlink to best run
    if [ -n "$best_run" ]; then
        mkdir -p "$BASE_OUTPUT_DIR/${dsl_basename}"
        ln -sfn "../${best_run}/${dsl_basename}" "$BASE_OUTPUT_DIR/${dsl_basename}/best"
        echo "$best_run (area/gates: $best_area)"
    else
        echo "No successful runs found"
    fi
}

# Export function for parallel execution
export -f run_synthesis
export EXTRA_ARGS BASE_OUTPUT_DIR VERBOSE RED GREEN YELLOW BLUE NC RUNS_PER_DSL

# Track start time
OVERALL_START=$(date +%s)

echo -e "${YELLOW}Starting synthesis jobs...${NC}"
echo ""

# Run jobs based on method
if [ "$USE_GNU_PARALLEL" = true ]; then
    # Use GNU parallel - generate all combinations of files and run numbers
    TOTAL_JOBS=$((${#DSL_FILES[@]} * RUNS_PER_DSL))

    # Generate all job combinations
    for dsl_file in "${DSL_FILES[@]}"; do
        for run_num in $(seq 1 $RUNS_PER_DSL); do
            echo "$dsl_file $run_num"
        done
    done | parallel -j "$MAX_PARALLEL" --line-buffer --colsep ' ' \
        --tagstring "[{#}/$TOTAL_JOBS]" \
        run_synthesis {1} {#} $TOTAL_JOBS {2}

    EXIT_CODE=$?

    # Select best run for each DSL
    if [ "$RUNS_PER_DSL" -gt 1 ]; then
        echo ""
        echo "Selecting best runs..."
        for dsl_file in "${DSL_FILES[@]}"; do
            dsl_basename=$(basename "$dsl_file" .dsl)
            echo -n "  $dsl_basename: "
            best=$(select_best_run "$dsl_basename")
            echo "$best"
        done
    fi
else
    # Use bash job control
    JOB_COUNT=0
    FAILED_JOBS=()
    TOTAL_JOBS=$((${#DSL_FILES[@]} * RUNS_PER_DSL))

    # Start all jobs, respecting MAX_PARALLEL limit
    for i in "${!DSL_FILES[@]}"; do
        dsl_file="${DSL_FILES[$i]}"
        dsl_basename=$(basename "$dsl_file" .dsl)

        # Run multiple times for each DSL
        for run_num in $(seq 1 $RUNS_PER_DSL); do
            # Calculate job number for display
            job_num=$(( i * RUNS_PER_DSL + run_num ))

            # Start job in background
            run_synthesis "$dsl_file" "$job_num" "$TOTAL_JOBS" "$run_num" &
            JOB_COUNT=$((JOB_COUNT + 1))

            # Throttle if needed
            if [ "$JOB_COUNT" -lt "$TOTAL_JOBS" ] && [ $(jobs -r | wc -l) -ge "$MAX_PARALLEL" ]; then
                # Wait for at least one job to finish before continuing
                while [ $(jobs -r | wc -l) -ge "$MAX_PARALLEL" ]; do
                    sleep 0.5
                done
            fi
        done
    done

    # Wait for all jobs to complete
    wait
    EXIT_CODE=$?

    # Select best run for each DSL
    if [ "$RUNS_PER_DSL" -gt 1 ]; then
        echo ""
        echo "Selecting best runs..."
        for dsl_file in "${DSL_FILES[@]}"; do
            dsl_basename=$(basename "$dsl_file" .dsl)
            echo -n "  $dsl_basename: "
            best=$(select_best_run "$dsl_basename")
            echo "$best"
        done
    fi
fi

# Calculate total time
OVERALL_END=$(date +%s)
OVERALL_DURATION=$((OVERALL_END - OVERALL_START))

# Print summary
echo ""
echo "=========================================="
echo "Batch Synthesis Summary"
echo "=========================================="
echo "Total time: ${OVERALL_DURATION} seconds"
echo "Output directory: $BASE_OUTPUT_DIR"

# List results
echo ""
echo "Results:"
for dsl_file in "${DSL_FILES[@]}"; do
    dsl_basename=$(basename "$dsl_file" .dsl)

    # Check for success based on whether we have multiple runs
    if [ "$RUNS_PER_DSL" -gt 1 ]; then
        # Check if any run succeeded
        success=false
        for run_num in $(seq 1 $RUNS_PER_DSL); do
            if [ -f "$BASE_OUTPUT_DIR/run_${run_num}/${dsl_basename}/ibex_optimized_post_abc.aig" ]; then
                success=true
                break
            fi
        done
        if [ "$success" = true ]; then
            echo -e "  ${GREEN}✓${NC} $dsl_basename"
        else
            echo -e "  ${RED}✗${NC} $dsl_basename"
        fi
    else
        # Single run - check directly
        if [ -f "$BASE_OUTPUT_DIR/${dsl_basename}/ibex_optimized_post_abc.aig" ]; then
            echo -e "  ${GREEN}✓${NC} $dsl_basename"
        else
            echo -e "  ${RED}✗${NC} $dsl_basename"
        fi
    fi
done

echo ""

# Generate comparison CSV if multiple files succeeded
SUCCESS_COUNT=0
for dsl_file in "${DSL_FILES[@]}"; do
    dsl_basename=$(basename "$dsl_file" .dsl)

    # Check for success based on whether we have multiple runs
    if [ "$RUNS_PER_DSL" -gt 1 ]; then
        # Check if any run succeeded
        for run_num in $(seq 1 $RUNS_PER_DSL); do
            if [ -f "$BASE_OUTPUT_DIR/run_${run_num}/${dsl_basename}/ibex_optimized_post_abc.aig" ]; then
                SUCCESS_COUNT=$((SUCCESS_COUNT + 1))
                break
            fi
        done
    else
        if [ -f "$BASE_OUTPUT_DIR/${dsl_basename}/ibex_optimized_post_abc.aig" ]; then
            SUCCESS_COUNT=$((SUCCESS_COUNT + 1))
        fi
    fi
done

if [ $SUCCESS_COUNT -gt 1 ]; then
    echo "Generating comparison report..."
    CSV_FILE="$BASE_OUTPUT_DIR/synthesis_comparison.csv"

    # Check if we have chip area data (from --gates)
    HAS_CHIP_AREA=false

    # Only check for chip area if --gates flag was specified
    if [[ "$EXTRA_ARGS" == *"--gates"* ]]; then
        for dsl_file in "${DSL_FILES[@]}"; do
            dsl_basename=$(basename "$dsl_file" .dsl)

            # Check appropriate location based on run count
            if [ "$RUNS_PER_DSL" -gt 1 ]; then
                # Check any run directory for chip area
                for run_num in $(seq 1 $RUNS_PER_DSL); do
                    synth_log="$BASE_OUTPUT_DIR/run_${run_num}/${dsl_basename}/synthesis.log"
                    if grep -q "Chip area:" "$synth_log" 2>/dev/null; then
                        HAS_CHIP_AREA=true
                        break 2  # Break both loops
                    fi
                done
            else
                # Single run - check base directory
                synth_log="$BASE_OUTPUT_DIR/${dsl_basename}/synthesis.log"
                if grep -q "Chip area:" "$synth_log" 2>/dev/null; then
                    HAS_CHIP_AREA=true
                    break
                fi
            fi
        done
    fi

    # Header - include chip area if available
    if [ "$HAS_CHIP_AREA" = true ]; then
        echo "DSL,Result_Type,Inputs,Outputs,Constraints,Latches,AND_gates,Levels,Chip_area_um2" > "$CSV_FILE"
    else
        echo "DSL,Result_Type,Inputs,Outputs,Constraints,Latches,AND_gates,Levels" > "$CSV_FILE"
    fi

    # Process each result
    for dsl_file in "${DSL_FILES[@]}"; do
        dsl_basename=$(basename "$dsl_file" .dsl)

        # Determine which directory to use
        if [ "$RUNS_PER_DSL" -gt 1 ] && [ -L "$BASE_OUTPUT_DIR/${dsl_basename}/best" ]; then
            result_dir="$BASE_OUTPUT_DIR/${dsl_basename}/best"
        else
            result_dir="$BASE_OUTPUT_DIR/${dsl_basename}"
        fi

        # Check if ODC-optimized results exist and are newer than baseline
        odc_optimized_log="$result_dir/odc_optimized_synthesis/abc.log"
        baseline_log="$result_dir/ibex_optimized_abc.log"

        if [ -f "$odc_optimized_log" ] && [ -f "$baseline_log" ]; then
            # Both exist - use the newer one
            if [ "$odc_optimized_log" -nt "$baseline_log" ]; then
                log_file="$odc_optimized_log"
                synth_log="$result_dir/odc_optimized_synthesis/synthesis.log"
            else
                log_file="$baseline_log"
                synth_log="$result_dir/synthesis.log"
            fi
        elif [ -f "$odc_optimized_log" ]; then
            # Only ODC exists
            log_file="$odc_optimized_log"
            synth_log="$result_dir/odc_optimized_synthesis/synthesis.log"
        else
            # Use baseline (or neither exists)
            log_file="$baseline_log"
            synth_log="$result_dir/synthesis.log"
        fi

        if [ -f "$log_file" ]; then
            # Determine which result type we're using for reporting
            result_type="baseline"
            if [[ "$log_file" == *"odc_optimized"* ]]; then
                result_type="ODC-optimized"
            fi

            # Extract final stats from ABC log
            # Format: "i/o = 1338/  432(c=1)  lat =  761  and =  14372  lev =115"
            stats=$(grep "i/o =" "$log_file" | tail -1)
            if [ ! -z "$stats" ]; then
                inputs=$(echo "$stats" | sed -n 's/.*i\/o = *\([0-9]*\).*/\1/p')
                outputs=$(echo "$stats" | sed -n 's/.*i\/o = *[0-9]*\/ *\([0-9]*\).*/\1/p')
                constraints=$(echo "$stats" | sed -n 's/.*c=\([0-9]*\).*/\1/p')
                latches=$(echo "$stats" | sed -n 's/.*lat = *\([0-9]*\).*/\1/p')
                and_gates=$(echo "$stats" | sed -n 's/.*and = *\([0-9]*\).*/\1/p')
                levels=$(echo "$stats" | sed -n 's/.*lev = *\([0-9]*\).*/\1/p')

                # Default to 0 if not found
                constraints=${constraints:-0}

                # Extract chip area if available (from gates.log)
                chip_area=""
                if [ "$HAS_CHIP_AREA" = true ]; then
                    # Check ODC-optimized gates.log first, then baseline
                    # Format: "Chip area for module 'name': 39250.144000"
                    if [ -f "$result_dir/odc_optimized_synthesis/ibex_alu_optimized_gates.log" ]; then
                        chip_area=$(grep "Chip area for module" "$result_dir/odc_optimized_synthesis/ibex_alu_optimized_gates.log" | tail -1 | awk '{print $NF}')
                    elif [ -f "$result_dir/ibex_optimized_gates.log" ]; then
                        chip_area=$(grep "Chip area for module" "$result_dir/ibex_optimized_gates.log" | tail -1 | awk '{print $NF}')
                    fi
                    chip_area=${chip_area:-"N/A"}
                fi

                if [ "$HAS_CHIP_AREA" = true ]; then
                    echo "$dsl_basename,$result_type,$inputs,$outputs,$constraints,$latches,$and_gates,$levels,$chip_area" >> "$CSV_FILE"
                else
                    echo "$dsl_basename,$result_type,$inputs,$outputs,$constraints,$latches,$and_gates,$levels" >> "$CSV_FILE"
                fi
            fi
        fi
    done

    echo -e "${GREEN}Comparison saved to: $CSV_FILE${NC}"

    # Show quick comparison
    echo ""
    if [ "$HAS_CHIP_AREA" = true ]; then
        echo "Quick comparison (sorted by chip area):"
        # Skip header, replace non-numeric chip area with a large value, sort by chip area column (9), show in table format
        tail -n +2 "$CSV_FILE" | awk -F',' '{
            # If chip area (column 9) is not a number, replace with a large value for sorting
            if ($9 !~ /^[0-9.]+$/) $9 = "999999999";
            print $0;
        }' OFS=',' | sort -t',' -k9 -g | head -10 | \
            awk -F',' 'BEGIN {printf "%-10s %-15s %8s %8s %12s\n", "DSL", "Result_Type", "AND_gates", "Levels", "Chip_area(µm²)"}
                       {printf "%-10s %-15s %8s %8s %12s\n", $1, $2, $7, $8, $9}'
    else
        echo "Quick comparison (sorted by AND gates):"
        sort -t',' -k7 -n "$CSV_FILE" | column -t -s',' | head -10
    fi
fi

exit $EXIT_CODE