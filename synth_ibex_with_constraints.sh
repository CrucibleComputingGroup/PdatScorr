#!/bin/bash
# End-to-end script: DSL file → Optimized Ibex RTLIL with instruction constraints
#
# Usage: ./synth_ibex_with_constraints.sh <rules.dsl> [output.il]

set -e

# Parse arguments
SYNTHESIZE_GATES=false
while [[ "$#" -gt 0 ]]; do
    case $1 in
        --gates) SYNTHESIZE_GATES=true; shift ;;
        -h|--help)
            echo "Usage: $0 [--gates] <rules.dsl> [output_dir|output.il]"
            echo ""
            echo "Generates optimized Ibex core with instruction constraints from DSL file"
            echo ""
            echo "Options:"
            echo "  --gates         Also synthesize to gate-level netlist with Skywater PDK"
            echo ""
            echo "Arguments:"
            echo "  rules.dsl       DSL file with instruction constraints"
            echo "  output_dir      Directory for all outputs (default: output/)"
            echo "  output.il       Specific output file path (if ends with .il)"
            echo ""
            echo "Examples:"
            echo "  $0 my_rules.dsl                         # RTLIL to output/ibex_optimized.il"
            echo "  $0 --gates my_rules.dsl                 # RTLIL + gate-level netlist"
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
CHECKER_SV="${BASE}_checker.sv"
ID_STAGE_SV="${BASE}_id_stage.sv"
SYNTH_SCRIPT="${BASE}_synth.ys"
PRE_ABC_IL="${BASE}_pre_abc.il"

echo "=========================================="
echo "Ibex Synthesis with Instruction Constraints"
echo "=========================================="
echo "Input DSL:    $INPUT_DSL"
echo "Output RTLIL: $OUTPUT_IL"
echo ""

# Determine total steps
if [ "$SYNTHESIZE_GATES" = true ]; then
    TOTAL_STEPS=5
else
    TOTAL_STEPS=4
fi

# Step 1: Generate checker module
echo "[1/$TOTAL_STEPS] Generating instruction checker..."
python3 generate_instruction_checker.py "$INPUT_DSL" "$CHECKER_SV"

if [ $? -ne 0 ]; then
    echo "ERROR: Failed to generate checker"
    exit 1
fi

# Step 2: Inject checker into ibex_id_stage.sv
echo "[2/$TOTAL_STEPS] Injecting checker into ibex_id_stage.sv..."
python3 inject_checker.py ./cores/ibex/rtl/ibex_id_stage.sv "$ID_STAGE_SV"

if [ $? -ne 0 ]; then
    echo "ERROR: Failed to inject checker"
    exit 1
fi

# Step 3: Generate synthesis script
echo "[3/$TOTAL_STEPS] Generating synthesis script..."
python3 make_synthesis_script.py "$CHECKER_SV" "$ID_STAGE_SV" \
    -o "$SYNTH_SCRIPT" -a "${BASE}"

if [ $? -ne 0 ]; then
    echo "ERROR: Failed to generate synthesis script"
    exit 1
fi

# Step 4: Run synthesis
echo "[4/$TOTAL_STEPS] Running synthesis with Synlig (this may take several minutes)..."
synlig -s "$SYNTH_SCRIPT"

if [ $? -ne 0 ]; then
    echo "ERROR: Synthesis failed"
    exit 1
fi

echo ""
echo "=========================================="
echo "SUCCESS!"
echo "=========================================="
echo "Generated files:"
echo "  - $CHECKER_SV (instruction checker module)"
echo "  - $ID_STAGE_SV (modified ibex_id_stage.sv)"
echo "  - $SYNTH_SCRIPT (synthesis script)"
echo "  - $PRE_ABC_IL (before ABC optimization)"
echo "  - $OUTPUT_IL (final optimized design)"
echo ""

# Step 5 (optional): Gate-level synthesis
if [ "$SYNTHESIZE_GATES" = true ]; then
    echo "[5/5] Synthesizing to gate level with Skywater PDK..."
    ./synth_to_gates.sh "$OUTPUT_IL"

    if [ $? -ne 0 ]; then
        echo "ERROR: Gate-level synthesis failed"
        exit 1
    fi
else
    echo "To synthesize to gates, run:"
    echo "  ./synth_to_gates.sh $OUTPUT_IL"
    echo "Or use --gates flag with this script."
fi

echo ""
echo "The design has been synthesized with ABC using your instruction"
echo "constraints (dc2, scorr, fraig). Logic for outlawed instructions"
echo "should be optimized away."
