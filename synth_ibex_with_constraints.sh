#!/bin/bash
# End-to-end script: DSL file → Optimized Ibex RTLIL with instruction constraints
#
# Usage: ./synth_ibex_with_constraints.sh <rules.dsl> [output.il]

set -e

# Parse arguments
SYNTHESIZE_GATES=false
ABC_DEPTH=2
WRITEBACK_STAGE=false
while [[ "$#" -gt 0 ]]; do
    case $1 in
        --gates) SYNTHESIZE_GATES=true; shift ;;
        --3stage) WRITEBACK_STAGE=true; ABC_DEPTH=3; shift ;;
        --abc-depth)
            ABC_DEPTH="$2"
            if ! [[ "$ABC_DEPTH" =~ ^[0-9]+$ ]] || [ "$ABC_DEPTH" -lt 1 ]; then
                echo "ERROR: --abc-depth must be a positive integer"
                exit 1
            fi
            shift 2
            ;;
        -h|--help)
            echo "Usage: $0 [OPTIONS] <rules.dsl> [output_dir|output.il]"
            echo ""
            echo "Generates optimized Ibex core with instruction constraints from DSL file"
            echo ""
            echo "Options:"
            echo "  --gates           Also synthesize to gate-level netlist with Skywater PDK"
            echo "  --3stage          Enable Ibex 3-stage pipeline (IF, ID/EX, WB) and set ABC depth=3"
            echo "  --abc-depth N     Set ABC k-induction depth (default: 2, matches 2-stage pipeline)"
            echo ""
            echo "Arguments:"
            echo "  rules.dsl       DSL file with instruction constraints"
            echo "  output_dir      Directory for all outputs (default: output/)"
            echo "  output.il       Specific output file path (if ends with .il)"
            echo ""
            echo "Examples:"
            echo "  $0 my_rules.dsl                         # RTLIL to output/ibex_optimized.il"
            echo "  $0 --gates my_rules.dsl                 # RTLIL + gate-level netlist"
            echo "  $0 --3stage my_rules.dsl                # Use 3-stage pipeline (tests k=3)"
            echo "  $0 --abc-depth 1 my_rules.dsl           # Try k=1 induction"
            echo "  $0 my_rules.dsl output/my_design        # Outputs to output/my_design/"
            echo "  $0 my_rules.dsl output/custom.il        # Outputs to output/custom.il"
            echo ""
            echo "All intermediate files are placed in the same directory as the final output."
            exit 0
            ;;
        *) break ;;
    esac
done

# Check DSL file exists
if [ "$#" -lt 1 ]; then
    echo "ERROR: Missing required argument <rules.dsl>"
    echo "Run with --help for usage information"
    exit 1
fi

# Check DSL file exists
if [ ! -f "$1" ]; then
    echo "ERROR: DSL file '$1' not found"
    exit 1
fi

INPUT_DSL="$1"

# Handle output argument:
# - If not provided: output/ibex_optimized.il
# - If ends with .il: use as full path
# - Otherwise: treat as directory and use ibex_optimized.il as filename
if [ -z "$2" ]; then
    OUTPUT_IL="output/ibex_optimized.il"
    OUTPUT_DIR="output"
elif [[ "$2" == *.il ]]; then
    OUTPUT_IL="$2"
    OUTPUT_DIR=$(dirname "$OUTPUT_IL")
else
    OUTPUT_DIR="$2"
    OUTPUT_IL="$OUTPUT_DIR/ibex_optimized.il"
fi

# Ensure output directory exists
mkdir -p "$OUTPUT_DIR"

# Derive intermediate filenames from output
BASE="${OUTPUT_IL%.il}"
ASSUMPTIONS_CODE="${BASE}_assumptions.sv"
ID_STAGE_SV="${BASE}_id_stage.sv"
SYNTH_SCRIPT="${BASE}_synth.ys"

echo "=========================================="
echo "Ibex Synthesis with Instruction Constraints"
echo "=========================================="
echo "Input DSL:    $INPUT_DSL"
echo "Output AIGER: ${BASE}_post_abc.aig"
echo ""

# Determine total steps
if [ "$SYNTHESIZE_GATES" = true ]; then
    TOTAL_STEPS=4
else
    TOTAL_STEPS=3
fi

# Step 1: Generate assumptions code (inline, no module)
echo "[1/$TOTAL_STEPS] Generating instruction assumptions..."
pdat-dsl codegen --inline "$INPUT_DSL" "$ASSUMPTIONS_CODE"

if [ $? -ne 0 ]; then
    echo "ERROR: Failed to generate assumptions"
    exit 1
fi

# Step 2: Inject assumptions into ibex_id_stage.sv
echo "[2/$TOTAL_STEPS] Injecting assumptions into ibex_id_stage.sv..."
python3 scripts/inject_checker.py --assumptions-file "$ASSUMPTIONS_CODE" ../CoreSim/cores/ibex/rtl/ibex_id_stage.sv "$ID_STAGE_SV"

if [ $? -ne 0 ]; then
    echo "ERROR: Failed to inject assumptions"
    exit 1
fi

# Step 3: Generate synthesis script
echo "[3/$TOTAL_STEPS] Generating synthesis script..."
if [ "$WRITEBACK_STAGE" = true ]; then
    echo "  Enabling 3-stage pipeline (WritebackStage=1)"
    python3 scripts/make_synthesis_script.py "$ID_STAGE_SV" \
        -o "$SYNTH_SCRIPT" -a "${BASE}" --writeback-stage
else
    python3 scripts/make_synthesis_script.py "$ID_STAGE_SV" \
        -o "$SYNTH_SCRIPT" -a "${BASE}"
fi

if [ $? -ne 0 ]; then
    echo "ERROR: Failed to generate synthesis script"
    exit 1
fi

# Step 4: Run synthesis
echo "[4/$TOTAL_STEPS] Running synthesis with Synlig (this may take several minutes)..."
YOSYS_LOG="${BASE}_yosys.log"
synlig -s "$SYNTH_SCRIPT" 2>&1 | tee "$YOSYS_LOG"

if [ ${PIPESTATUS[0]} -ne 0 ]; then
    echo "ERROR: Synthesis failed"
    exit 1
fi

echo ""
echo "=========================================="
echo "SUCCESS!"
echo "=========================================="
echo "Generated files:"
echo "  - $ASSUMPTIONS_CODE (assumption code)"
echo "  - $ID_STAGE_SV (modified ibex_id_stage.sv with assumptions)"
echo "  - $SYNTH_SCRIPT (synthesis script)"
echo "  - ${BASE}_pre_abc.aig (AIGER for external ABC)"
echo "  - $YOSYS_LOG (Yosys synthesis log)"
echo ""

# Step 5: Run external ABC if available
if command -v abc &> /dev/null; then
    ABC_INPUT="${BASE}_pre_abc.aig"
    ABC_OUTPUT="${BASE}_post_abc.aig"
    ABC_LOG="${BASE}_abc.log"

    if [ -f "$ABC_INPUT" ] && [ -s "$ABC_INPUT" ]; then
        echo "Running external ABC with sequential optimization (scorr)..."
        echo "Input:  $ABC_INPUT"
        echo "Output: $ABC_OUTPUT"
        echo ""

        echo "ABC k-induction depth: $ABC_DEPTH (should match pipeline depth)"
        abc -c "read_aiger $ABC_INPUT; print_stats; strash; print_stats; cycle 100; scorr -c -F $ABC_DEPTH -v; print_stats; dc2; dretime; write_aiger $ABC_OUTPUT" 2>&1 | tee "$ABC_LOG" | grep -E "^output|i/o =|lat =|and =|constraint|Removed equivs"

        if [ ${PIPESTATUS[0]} -eq 0 ] && [ -f "$ABC_OUTPUT" ]; then
            echo ""
            echo "External ABC optimization completed!"
            echo "  - $ABC_OUTPUT (optimized AIGER)"
            echo "  - $ABC_LOG (ABC optimization log)"
        else
            echo "WARNING: External ABC optimization failed"
        fi
    fi
else
    echo "External ABC not found - skipping sequential optimization"
    echo "Install from: https://github.com/berkeley-abc/abc"
fi

echo ""

# Step 6 (optional): Gate-level synthesis
if [ "$SYNTHESIZE_GATES" = true ]; then
    echo "Synthesizing to gate level with Skywater PDK..."
    ./scripts/synth_to_gates.sh "$BASE"

    if [ $? -ne 0 ]; then
        echo "ERROR: Gate-level synthesis failed"
        exit 1
    fi
else
    echo "To synthesize to gates, run:"
    echo "  ./scripts/synth_to_gates.sh $BASE"
    echo "Or use --gates flag with this script."
fi

echo ""
echo "The design has been synthesized with constraints. Logic for outlawed"
echo "instructions should be optimized away via assumptions and ABC optimization."
