#!/bin/bash
# Simple parallel batch comparison script

DSL_FILE="${1:-../PdatDsl/examples/rv32im.dsl}"
BASE_OUTPUT="${2:-output/comparison}"
TIMESTAMP=$(date +%Y%m%d_%H%M%S)

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
echo ""

# Create all directories
mkdir -p "$OUTPUT_DIR"
for depth in 2 3 4 5; do
    mkdir -p "${OUTPUT_DIR}/isa_only/depth_${depth}"
    mkdir -p "${OUTPUT_DIR}/with_timing/depth_${depth}"
    mkdir -p "${OUTPUT_DIR}/isa_only_3stage/depth_${depth}"
    mkdir -p "${OUTPUT_DIR}/with_timing_3stage/depth_${depth}"
done

echo "Launching all synthesis jobs in parallel..."

# Launch all jobs with & - SIMPLE!
# ISA-only jobs
./synth_ibex_with_constraints.sh --gates --abc-depth 2 "$DSL_FILE" "${OUTPUT_DIR}/isa_only/depth_2" > "${OUTPUT_DIR}/isa_only/depth_2/synthesis.log" 2>&1 &
./synth_ibex_with_constraints.sh --gates --abc-depth 3 "$DSL_FILE" "${OUTPUT_DIR}/isa_only/depth_3" > "${OUTPUT_DIR}/isa_only/depth_3/synthesis.log" 2>&1 &
./synth_ibex_with_constraints.sh --gates --abc-depth 4 "$DSL_FILE" "${OUTPUT_DIR}/isa_only/depth_4" > "${OUTPUT_DIR}/isa_only/depth_4/synthesis.log" 2>&1 &
./synth_ibex_with_constraints.sh --gates --abc-depth 5 "$DSL_FILE" "${OUTPUT_DIR}/isa_only/depth_5" > "${OUTPUT_DIR}/isa_only/depth_5/synthesis.log" 2>&1 &

# ISA+timing jobs
./synth_ibex_with_isa_and_timing.sh --gates --abc-depth 2 "$DSL_FILE" "${OUTPUT_DIR}/with_timing/depth_2" > "${OUTPUT_DIR}/with_timing/depth_2/synthesis.log" 2>&1 &
./synth_ibex_with_isa_and_timing.sh --gates --abc-depth 3 "$DSL_FILE" "${OUTPUT_DIR}/with_timing/depth_3" > "${OUTPUT_DIR}/with_timing/depth_3/synthesis.log" 2>&1 &
./synth_ibex_with_isa_and_timing.sh --gates --abc-depth 4 "$DSL_FILE" "${OUTPUT_DIR}/with_timing/depth_4" > "${OUTPUT_DIR}/with_timing/depth_4/synthesis.log" 2>&1 &
./synth_ibex_with_isa_and_timing.sh --gates --abc-depth 5 "$DSL_FILE" "${OUTPUT_DIR}/with_timing/depth_5" > "${OUTPUT_DIR}/with_timing/depth_5/synthesis.log" 2>&1 &

# 3-stage pipeline variants (depth >= 3)
./synth_ibex_with_constraints.sh --gates --3stage --abc-depth 3 "$DSL_FILE" "${OUTPUT_DIR}/isa_only_3stage/depth_3" > "${OUTPUT_DIR}/isa_only_3stage/depth_3/synthesis.log" 2>&1 &
./synth_ibex_with_constraints.sh --gates --3stage --abc-depth 4 "$DSL_FILE" "${OUTPUT_DIR}/isa_only_3stage/depth_4" > "${OUTPUT_DIR}/isa_only_3stage/depth_4/synthesis.log" 2>&1 &
./synth_ibex_with_constraints.sh --gates --3stage --abc-depth 5 "$DSL_FILE" "${OUTPUT_DIR}/isa_only_3stage/depth_5" > "${OUTPUT_DIR}/isa_only_3stage/depth_5/synthesis.log" 2>&1 &

./synth_ibex_with_isa_and_timing.sh --gates --3stage --abc-depth 3 "$DSL_FILE" "${OUTPUT_DIR}/with_timing_3stage/depth_3" > "${OUTPUT_DIR}/with_timing_3stage/depth_3/synthesis.log" 2>&1 &
./synth_ibex_with_isa_and_timing.sh --gates --3stage --abc-depth 4 "$DSL_FILE" "${OUTPUT_DIR}/with_timing_3stage/depth_4" > "${OUTPUT_DIR}/with_timing_3stage/depth_4/synthesis.log" 2>&1 &
./synth_ibex_with_isa_and_timing.sh --gates --3stage --abc-depth 5 "$DSL_FILE" "${OUTPUT_DIR}/with_timing_3stage/depth_5" > "${OUTPUT_DIR}/with_timing_3stage/depth_5/synthesis.log" 2>&1 &

echo "Launched 14 parallel jobs"
echo "Waiting for all jobs to complete..."

# Wait for all background jobs
wait

echo ""
echo "All jobs completed!"
echo ""

# Generate summary
echo "=========================================="
echo "Results Summary (Chip Area in µm²)"
echo "=========================================="

# Simple comparison - show actual chip area from gate synthesis
for depth in 2 3 4 5; do
    echo ""
    echo "ABC Depth $depth:"

    # Check ISA-only (2-stage)
    GATES_LOG="${OUTPUT_DIR}/isa_only/depth_${depth}/${DSL_BASENAME}/ibex_optimized_gates.log"
    if [ -f "$GATES_LOG" ]; then
        AREA=$(grep "Chip area for module" "$GATES_LOG" 2>/dev/null | tail -1 | sed 's/.*: //' | sed 's/ µm²//')
        if [ -n "$AREA" ]; then
            echo "  ISA-only (2-stage):     $AREA µm²"
        else
            echo "  ISA-only (2-stage):     No area data"
        fi
    else
        echo "  ISA-only (2-stage):     FAILED or not synthesized to gates"
    fi

    # Check ISA+timing (2-stage)
    GATES_LOG="${OUTPUT_DIR}/with_timing/depth_${depth}/${DSL_BASENAME}_timing/ibex_optimized_gates.log"
    if [ -f "$GATES_LOG" ]; then
        AREA=$(grep "Chip area for module" "$GATES_LOG" 2>/dev/null | tail -1 | sed 's/.*: //' | sed 's/ µm²//')
        if [ -n "$AREA" ]; then
            echo "  ISA+timing (2-stage):   $AREA µm²"
        else
            echo "  ISA+timing (2-stage):   No area data"
        fi
    else
        echo "  ISA+timing (2-stage):   FAILED or not synthesized to gates"
    fi

    # Check 3-stage if depth >= 3
    if [ $depth -ge 3 ]; then
        GATES_LOG="${OUTPUT_DIR}/isa_only_3stage/depth_${depth}/${DSL_BASENAME}/ibex_optimized_gates.log"
        if [ -f "$GATES_LOG" ]; then
            AREA=$(grep "Chip area for module" "$GATES_LOG" 2>/dev/null | tail -1 | sed 's/.*: //' | sed 's/ µm²//')
            if [ -n "$AREA" ]; then
                echo "  ISA-only (3-stage):     $AREA µm²"
            else
                echo "  ISA-only (3-stage):     No area data"
            fi
        else
            echo "  ISA-only (3-stage):     FAILED or not synthesized to gates"
        fi

        GATES_LOG="${OUTPUT_DIR}/with_timing_3stage/depth_${depth}/${DSL_BASENAME}_timing/ibex_optimized_gates.log"
        if [ -f "$GATES_LOG" ]; then
            AREA=$(grep "Chip area for module" "$GATES_LOG" 2>/dev/null | tail -1 | sed 's/.*: //' | sed 's/ µm²//')
            if [ -n "$AREA" ]; then
                echo "  ISA+timing (3-stage):   $AREA µm²"
            else
                echo "  ISA+timing (3-stage):   No area data"
            fi
        else
            echo "  ISA+timing (3-stage):   FAILED or not synthesized to gates"
        fi
    fi
done

# Also create a CSV file for easy analysis
echo ""
echo "Creating CSV file for analysis..."
CSV_FILE="${OUTPUT_DIR}/area_comparison.csv"
echo "Configuration,ABC_Depth,Chip_Area_um2" > "$CSV_FILE"

for depth in 2 3 4 5; do
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

    # 3-stage variants
    if [ $depth -ge 3 ]; then
        GATES_LOG="${OUTPUT_DIR}/isa_only_3stage/depth_${depth}/${DSL_BASENAME}/ibex_optimized_gates.log"
        if [ -f "$GATES_LOG" ]; then
            AREA=$(grep "Chip area for module" "$GATES_LOG" 2>/dev/null | tail -1 | sed 's/.*: //' | sed 's/ µm²//' | sed 's/,//g')
            [ -n "$AREA" ] && echo "ISA_only_3stage,$depth,$AREA" >> "$CSV_FILE"
        fi

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