#!/bin/bash
# Simple parallel batch comparison script with configurable depth array

# ========================================
# Configuration
# ========================================
DSL_FILE="${1:-../PdatDsl/examples/rv32im.dsl}"
BASE_OUTPUT="${2:-output/comparison}"
TIMESTAMP=$(date +%Y%m%d_%H%M%S)

# ABC depths to test - EASILY CONFIGURABLE!
# Just add/remove depths here to change what's tested
ABC_DEPTHS=(2 3 4 5 6 7 8)
# Example: ABC_DEPTHS=(2 3 4 5 6 7) for extended testing

# Minimum depth for 3-stage pipeline testing
MIN_3STAGE_DEPTH=3

# ========================================
# Setup
# ========================================
if [ ! -f "$DSL_FILE" ]; then
    echo "ERROR: DSL file '$DSL_FILE' not found"
    exit 1
fi

DSL_BASENAME=$(basename "$DSL_FILE" .dsl)
OUTPUT_DIR="${BASE_OUTPUT}/${DSL_BASENAME}_${TIMESTAMP}"

echo "=========================================="
echo "Batch Synthesis Comparison (PARALLEL)"
echo "=========================================="
echo "DSL file: $DSL_FILE"
echo "Output dir: $OUTPUT_DIR"
echo "ABC depths: ${ABC_DEPTHS[*]}"
echo ""

# Create all directories
mkdir -p "$OUTPUT_DIR"
for depth in "${ABC_DEPTHS[@]}"; do
    mkdir -p "${OUTPUT_DIR}/isa_only/depth_${depth}"
    mkdir -p "${OUTPUT_DIR}/with_timing/depth_${depth}"
    if [ "$depth" -ge "$MIN_3STAGE_DEPTH" ]; then
        mkdir -p "${OUTPUT_DIR}/isa_only_3stage/depth_${depth}"
        mkdir -p "${OUTPUT_DIR}/with_timing_3stage/depth_${depth}"
    fi
done

echo "Launching all synthesis jobs in parallel..."

# ========================================
# Launch Jobs using Arrays
# ========================================
declare -a job_pids=()

# Launch 2-stage ISA-only jobs
for depth in "${ABC_DEPTHS[@]}"; do
    ./synth_ibex_with_constraints.sh --gates --abc-depth "$depth" "$DSL_FILE" \
        "${OUTPUT_DIR}/isa_only/depth_${depth}" \
        > "${OUTPUT_DIR}/isa_only/depth_${depth}/synthesis.log" 2>&1 &
    job_pids+=($!)
done

# Launch 2-stage ISA+timing jobs
for depth in "${ABC_DEPTHS[@]}"; do
    ./synth_ibex_with_isa_and_timing.sh --gates --abc-depth "$depth" "$DSL_FILE" \
        "${OUTPUT_DIR}/with_timing/depth_${depth}" \
        > "${OUTPUT_DIR}/with_timing/depth_${depth}/synthesis.log" 2>&1 &
    job_pids+=($!)
done

# Launch 3-stage ISA-only jobs (for depths >= MIN_3STAGE_DEPTH)
for depth in "${ABC_DEPTHS[@]}"; do
    if [ "$depth" -ge "$MIN_3STAGE_DEPTH" ]; then
        ./synth_ibex_with_constraints.sh --gates --3stage --abc-depth "$depth" "$DSL_FILE" \
            "${OUTPUT_DIR}/isa_only_3stage/depth_${depth}" \
            > "${OUTPUT_DIR}/isa_only_3stage/depth_${depth}/synthesis.log" 2>&1 &
        job_pids+=($!)
    fi
done

# Launch 3-stage ISA+timing jobs (for depths >= MIN_3STAGE_DEPTH)
for depth in "${ABC_DEPTHS[@]}"; do
    if [ "$depth" -ge "$MIN_3STAGE_DEPTH" ]; then
        ./synth_ibex_with_isa_and_timing.sh --gates --3stage --abc-depth "$depth" "$DSL_FILE" \
            "${OUTPUT_DIR}/with_timing_3stage/depth_${depth}" \
            > "${OUTPUT_DIR}/with_timing_3stage/depth_${depth}/synthesis.log" 2>&1 &
        job_pids+=($!)
    fi
done

echo "Launched ${#job_pids[@]} parallel jobs"
echo "Waiting for all jobs to complete..."

# Wait for all background jobs
wait

echo ""
echo "All jobs completed!"
echo ""

# ========================================
# Generate Summary
# ========================================
echo "=========================================="
echo "Results Summary (Chip Area in µm²)"
echo "=========================================="

# Function to extract area from log file
extract_area() {
    local log_file="$1"
    if [ -f "$log_file" ]; then
        local area=$(grep "Chip area for module" "$log_file" 2>/dev/null | tail -1 | sed 's/.*: //' | sed 's/ µm²//')
        if [ -n "$area" ]; then
            echo "$area"
        else
            echo "NO_DATA"
        fi
    else
        echo "FAILED"
    fi
}

# Print results for each depth
for depth in "${ABC_DEPTHS[@]}"; do
    echo ""
    echo "ABC Depth $depth:"

    # ISA-only (2-stage)
    AREA=$(extract_area "${OUTPUT_DIR}/isa_only/depth_${depth}/${DSL_BASENAME}/ibex_optimized_gates.log")
    if [ "$AREA" = "FAILED" ]; then
        echo "  ISA-only (2-stage):     FAILED or not synthesized to gates"
    elif [ "$AREA" = "NO_DATA" ]; then
        echo "  ISA-only (2-stage):     No area data"
    else
        echo "  ISA-only (2-stage):     $AREA µm²"
    fi

    # ISA+timing (2-stage)
    AREA=$(extract_area "${OUTPUT_DIR}/with_timing/depth_${depth}/${DSL_BASENAME}_timing/ibex_optimized_gates.log")
    if [ "$AREA" = "FAILED" ]; then
        echo "  ISA+timing (2-stage):   FAILED or not synthesized to gates"
    elif [ "$AREA" = "NO_DATA" ]; then
        echo "  ISA+timing (2-stage):   No area data"
    else
        echo "  ISA+timing (2-stage):   $AREA µm²"
    fi

    # 3-stage variants (if depth >= MIN_3STAGE_DEPTH)
    if [ "$depth" -ge "$MIN_3STAGE_DEPTH" ]; then
        # ISA-only (3-stage)
        AREA=$(extract_area "${OUTPUT_DIR}/isa_only_3stage/depth_${depth}/${DSL_BASENAME}/ibex_optimized_gates.log")
        if [ "$AREA" = "FAILED" ]; then
            echo "  ISA-only (3-stage):     FAILED or not synthesized to gates"
        elif [ "$AREA" = "NO_DATA" ]; then
            echo "  ISA-only (3-stage):     No area data"
        else
            echo "  ISA-only (3-stage):     $AREA µm²"
        fi

        # ISA+timing (3-stage)
        AREA=$(extract_area "${OUTPUT_DIR}/with_timing_3stage/depth_${depth}/${DSL_BASENAME}_timing/ibex_optimized_gates.log")
        if [ "$AREA" = "FAILED" ]; then
            echo "  ISA+timing (3-stage):   FAILED or not synthesized to gates"
        elif [ "$AREA" = "NO_DATA" ]; then
            echo "  ISA+timing (3-stage):   No area data"
        else
            echo "  ISA+timing (3-stage):   $AREA µm²"
        fi
    fi
done

# ========================================
# Create CSV File
# ========================================
echo ""
echo "Creating CSV file for analysis..."
CSV_FILE="${OUTPUT_DIR}/area_comparison.csv"
echo "Configuration,ABC_Depth,Chip_Area_um2" > "$CSV_FILE"

for depth in "${ABC_DEPTHS[@]}"; do
    # ISA-only (2-stage)
    GATES_LOG="${OUTPUT_DIR}/isa_only/depth_${depth}/${DSL_BASENAME}/ibex_optimized_gates.log"
    if [ -f "$GATES_LOG" ]; then
        AREA=$(grep "Chip area for module" "$GATES_LOG" 2>/dev/null | tail -1 | sed 's/.*: //' | sed 's/ µm²//' | sed 's/,//g')
        [ -n "$AREA" ] && echo "ISA_only_2stage,$depth,$AREA" >> "$CSV_FILE"
    fi

    # ISA+timing (2-stage)
    GATES_LOG="${OUTPUT_DIR}/with_timing/depth_${depth}/${DSL_BASENAME}_timing/ibex_optimized_gates.log"
    if [ -f "$GATES_LOG" ]; then
        AREA=$(grep "Chip area for module" "$GATES_LOG" 2>/dev/null | tail -1 | sed 's/.*: //' | sed 's/ µm²//' | sed 's/,//g')
        [ -n "$AREA" ] && echo "ISA+timing_2stage,$depth,$AREA" >> "$CSV_FILE"
    fi

    # 3-stage variants (if depth >= MIN_3STAGE_DEPTH)
    if [ $depth -ge "$MIN_3STAGE_DEPTH" ]; then
        # ISA-only (3-stage)
        GATES_LOG="${OUTPUT_DIR}/isa_only_3stage/depth_${depth}/${DSL_BASENAME}/ibex_optimized_gates.log"
        if [ -f "$GATES_LOG" ]; then
            AREA=$(grep "Chip area for module" "$GATES_LOG" 2>/dev/null | tail -1 | sed 's/.*: //' | sed 's/ µm²//' | sed 's/,//g')
            [ -n "$AREA" ] && echo "ISA_only_3stage,$depth,$AREA" >> "$CSV_FILE"
        fi

        # ISA+timing (3-stage)
        GATES_LOG="${OUTPUT_DIR}/with_timing_3stage/depth_${depth}/${DSL_BASENAME}_timing/ibex_optimized_gates.log"
        if [ -f "$GATES_LOG" ]; then
            AREA=$(grep "Chip area for module" "$GATES_LOG" 2>/dev/null | tail -1 | sed 's/.*: //' | sed 's/ µm²//' | sed 's/,//g')
            [ -n "$AREA" ] && echo "ISA+timing_3stage,$depth,$AREA" >> "$CSV_FILE"
        fi
    fi
done

echo "CSV saved to: $CSV_FILE"

echo ""
echo "Results saved to: $OUTPUT_DIR"
