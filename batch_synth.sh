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
        -o|--output-dir)
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
        --gnu-parallel)
            USE_GNU_PARALLEL=true
            shift
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
            echo "  -j, --jobs N          Maximum parallel jobs (default: 4)"
            echo "  -o, --output-dir DIR  Base output directory (default: output)"
            echo "  --gates               Pass --gates to synthesis script"
            echo "  --3stage              Pass --3stage to synthesis script"
            echo "  --abc-depth N         Pass --abc-depth N to synthesis script"
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
if [ ! -f "./synth_ibex_with_constraints.sh" ]; then
    echo -e "${RED}Error: synth_ibex_with_constraints.sh not found in current directory${NC}"
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

    # Get base name for status display
    local dsl_basename=$(basename "$dsl_file" .dsl)

    # Determine log file location
    local log_file="$BASE_OUTPUT_DIR/${dsl_basename}/synthesis.log"
    mkdir -p "$BASE_OUTPUT_DIR/${dsl_basename}"

    # Print start message
    echo -e "${BLUE}[$job_num/$total_jobs] Starting: ${dsl_basename}${NC}"

    # Run synthesis
    local start_time=$(date +%s)

    if [ "$VERBOSE" = true ]; then
        # Show output directly
        ./synth_ibex_with_constraints.sh $EXTRA_ARGS "$dsl_file" "$BASE_OUTPUT_DIR" 2>&1 | tee "$log_file"
        local exit_code=${PIPESTATUS[0]}
    else
        # Redirect to log file
        ./synth_ibex_with_constraints.sh $EXTRA_ARGS "$dsl_file" "$BASE_OUTPUT_DIR" > "$log_file" 2>&1
        local exit_code=$?
    fi

    local end_time=$(date +%s)
    local duration=$((end_time - start_time))

    # Print completion message
    if [ $exit_code -eq 0 ]; then
        echo -e "${GREEN}[$job_num/$total_jobs] ✓ Completed: ${dsl_basename} (${duration}s)${NC}"
        # Show key metrics if available
        if [ -f "$BASE_OUTPUT_DIR/${dsl_basename}/ibex_optimized_abc.log" ]; then
            local stats=$(grep "and =" "$BASE_OUTPUT_DIR/${dsl_basename}/ibex_optimized_abc.log" | tail -1)
            if [ ! -z "$stats" ]; then
                echo "  └─ Final: $stats"
            fi
        fi
    else
        echo -e "${RED}[$job_num/$total_jobs] ✗ Failed: ${dsl_basename} (${duration}s)${NC}"
        echo "  └─ Check log: $log_file"
    fi

    return $exit_code
}

# Export function for parallel execution
export -f run_synthesis
export EXTRA_ARGS BASE_OUTPUT_DIR VERBOSE RED GREEN YELLOW BLUE NC

# Track start time
OVERALL_START=$(date +%s)

echo -e "${YELLOW}Starting synthesis jobs...${NC}"
echo ""

# Run jobs based on method
if [ "$USE_GNU_PARALLEL" = true ]; then
    # Use GNU parallel
    printf '%s\n' "${DSL_FILES[@]}" | \
        parallel -j "$MAX_PARALLEL" --line-buffer --tagstring "[{#}/${#DSL_FILES[@]}]" \
        run_synthesis {} {#} ${#DSL_FILES[@]}
    EXIT_CODE=$?
else
    # Use bash job control
    JOB_COUNT=0
    FAILED_JOBS=()

    # Start all jobs, respecting MAX_PARALLEL limit
    for i in "${!DSL_FILES[@]}"; do
        dsl_file="${DSL_FILES[$i]}"
        job_num=$((i + 1))

        # Start job in background
        run_synthesis "$dsl_file" "$job_num" "${#DSL_FILES[@]}" &
        JOB_COUNT=$((JOB_COUNT + 1))

        # Only throttle if we have more files than max parallel
        # and we haven't started the last job yet
        if [ "$JOB_COUNT" -lt "${#DSL_FILES[@]}" ] && [ "$JOB_COUNT" -ge "$MAX_PARALLEL" ]; then
            # Wait for at least one job to finish before continuing
            while [ $(jobs -r | wc -l) -ge "$MAX_PARALLEL" ]; do
                sleep 0.5
            done
        fi
    done

    # Wait for all jobs to complete
    wait
    EXIT_CODE=$?
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
    if [ -f "$BASE_OUTPUT_DIR/${dsl_basename}/ibex_optimized_post_abc.aig" ]; then
        echo -e "  ${GREEN}✓${NC} $dsl_basename"
    else
        echo -e "  ${RED}✗${NC} $dsl_basename"
    fi
done

echo ""

# Generate comparison CSV if multiple files succeeded
SUCCESS_COUNT=0
for dsl_file in "${DSL_FILES[@]}"; do
    dsl_basename=$(basename "$dsl_file" .dsl)
    if [ -f "$BASE_OUTPUT_DIR/${dsl_basename}/ibex_optimized_post_abc.aig" ]; then
        SUCCESS_COUNT=$((SUCCESS_COUNT + 1))
    fi
done

if [ $SUCCESS_COUNT -gt 1 ]; then
    echo "Generating comparison report..."
    CSV_FILE="$BASE_OUTPUT_DIR/synthesis_comparison.csv"

    # Check if we have chip area data (from --gates)
    HAS_CHIP_AREA=false
    for dsl_file in "${DSL_FILES[@]}"; do
        dsl_basename=$(basename "$dsl_file" .dsl)
        synth_log="$BASE_OUTPUT_DIR/${dsl_basename}/synthesis.log"
        if grep -q "Chip area:" "$synth_log" 2>/dev/null; then
            HAS_CHIP_AREA=true
            break
        fi
    done

    # Header - include chip area if available
    if [ "$HAS_CHIP_AREA" = true ]; then
        echo "DSL,Inputs,Outputs,Constraints,Latches,AND_gates,Levels,Chip_area_um2" > "$CSV_FILE"
    else
        echo "DSL,Inputs,Outputs,Constraints,Latches,AND_gates,Levels" > "$CSV_FILE"
    fi

    # Process each result
    for dsl_file in "${DSL_FILES[@]}"; do
        dsl_basename=$(basename "$dsl_file" .dsl)
        log_file="$BASE_OUTPUT_DIR/${dsl_basename}/ibex_optimized_abc.log"
        synth_log="$BASE_OUTPUT_DIR/${dsl_basename}/synthesis.log"

        if [ -f "$log_file" ]; then
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

                # Extract chip area if available
                chip_area=""
                if [ "$HAS_CHIP_AREA" = true ] && [ -f "$synth_log" ]; then
                    # Format: "Chip area: 41676.220800 µm²"
                    chip_area=$(grep "Chip area:" "$synth_log" | tail -1 | sed -n 's/.*Chip area: *\([0-9]*\.?[0-9]*\).*/\1/p')
                    chip_area=${chip_area:-"N/A"}
                fi

                if [ "$HAS_CHIP_AREA" = true ]; then
                    echo "$dsl_basename,$inputs,$outputs,$constraints,$latches,$and_gates,$levels,$chip_area" >> "$CSV_FILE"
                else
                    echo "$dsl_basename,$inputs,$outputs,$constraints,$latches,$and_gates,$levels" >> "$CSV_FILE"
                fi
            fi
        fi
    done

    echo -e "${GREEN}Comparison saved to: $CSV_FILE${NC}"

    # Show quick comparison
    echo ""
    if [ "$HAS_CHIP_AREA" = true ]; then
        echo "Quick comparison (sorted by chip area):"
        # Skip header, sort by chip area column (8), show in table format
        tail -n +2 "$CSV_FILE" | sort -t',' -k8 -g | head -10 | \
            awk -F',' 'BEGIN {printf "%-20s %8s %8s %12s\n", "DSL", "AND_gates", "Levels", "Chip_area(µm²)"}
                       {printf "%-20s %8s %8s %12s\n", $1, $6, $7, $8}'
    else
        echo "Quick comparison (sorted by AND gates):"
        sort -t',' -k6 -n "$CSV_FILE" | column -t -s',' | head -10
    fi
fi

exit $EXIT_CODE