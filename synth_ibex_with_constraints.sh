#!/bin/bash
# End-to-end script: DSL file → Optimized Ibex RTLIL with instruction constraints
#
# Usage: ./synth_ibex_with_constraints.sh <rules.dsl> [output.il]

set -e

# Parse arguments
SYNTHESIZE_GATES=false
ABC_DEPTH=2
WRITEBACK_STAGE=false
CONFIG_FILE=""
CORE_NAME=""
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
        --config)
            CONFIG_FILE="$2"
            shift 2
            ;;
        --core)
            CORE_NAME="$2"
            shift 2
            ;;
        -h|--help)
            echo "Usage: $0 [OPTIONS] <rules.dsl> [output_dir|output.il]"
            echo ""
            echo "Generates optimized RISC-V core with instruction constraints from DSL file"
            echo ""
            echo "Options:"
            echo "  --gates           Also synthesize to gate-level netlist with Skywater PDK"
            echo "  --3stage          Enable Ibex 3-stage pipeline (IF, ID/EX, WB) and set ABC depth=3"
            echo "  --abc-depth N     Set ABC k-induction depth (default: 2, matches 2-stage pipeline)"
            echo "  --config FILE     Use YAML config file (enables config mode)"
            echo "  --core NAME       Core name for auto-config lookup (default: ibex, looks for configs/NAME.yaml)"
            echo ""
            echo "Arguments:"
            echo "  rules.dsl       DSL file with instruction constraints"
            echo "  output_dir      Base directory for outputs (default: output/)"
            echo "  output.il       Specific output file path (if ends with .il)"
            echo ""
            echo "Config Mode:"
            echo "  When --config or --core is specified, source files and paths are read from"
            echo "  a YAML configuration file instead of being hardcoded. This allows supporting"
            echo "  multiple cores (Ibex, BOOM, Rocket, etc.) with the same script."
            echo ""
            echo "Output organization:"
            echo "  - Files are organized in subfolders named after the DSL file"
            echo "  - e.g., my_rules.dsl → output/my_rules/ibex_optimized.il"
            echo ""
            echo "Examples:"
            echo "  $0 my_rules.dsl                         # Outputs to output/my_rules/"
            echo "  $0 --gates my_rules.dsl                 # RTLIL + gates in output/my_rules/"
            echo "  $0 --3stage my_rules.dsl                # 3-stage pipeline in output/my_rules/"
            echo "  $0 --abc-depth 1 my_rules.dsl           # k=1 induction in output/my_rules/"
            echo "  $0 my_rules.dsl results                 # Outputs to results/my_rules/"
            echo "  $0 my_rules.dsl output/custom.il        # Specific path output/custom.il"
            echo "  $0 --config configs/ibex.yaml my_rules.dsl    # Use config file"
            echo "  $0 --core ibex my_rules.dsl             # Auto-load configs/ibex.yaml"
            echo ""
            echo "All intermediate files are placed in the same directory as the final output."
            exit 0
            ;;
        *) break ;;
    esac
done

# Handle --core flag: auto-find config file
if [ -n "$CORE_NAME" ] && [ -z "$CONFIG_FILE" ]; then
    CONFIG_FILE="configs/${CORE_NAME}.yaml"
    if [ ! -f "$CONFIG_FILE" ]; then
        echo "ERROR: Config file not found: $CONFIG_FILE"
        echo "Available configs:"
        ls -1 configs/*.yaml 2>/dev/null | grep -v schema.yaml | sed 's/configs\//  - /' || echo "  (none)"
        exit 1
    fi
    echo "Using config file: $CONFIG_FILE"
fi

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

# Extract DSL base name (without path and extension) for subfolder
DSL_BASENAME=$(basename "$INPUT_DSL" .dsl)

# Handle output argument:
# - If not provided: output/<dsl_name>/ibex_optimized.il
# - If ends with .il: use as full path
# - Otherwise: treat as directory and use <dsl_name>/ibex_optimized.il
if [ -z "$2" ]; then
    OUTPUT_DIR="output/$DSL_BASENAME"
    OUTPUT_IL="$OUTPUT_DIR/ibex_optimized.il"
elif [[ "$2" == *.il ]]; then
    OUTPUT_IL="$2"
    OUTPUT_DIR=$(dirname "$OUTPUT_IL")
else
    OUTPUT_DIR="$2/$DSL_BASENAME"
    OUTPUT_IL="$OUTPUT_DIR/ibex_optimized.il"
fi

# Ensure output directory exists
mkdir -p "$OUTPUT_DIR"

# Derive intermediate filenames from output
BASE="${OUTPUT_IL%.il}"
ASSUMPTIONS_CODE="${BASE}_assumptions.sv"
ID_STAGE_SV="${BASE}_id_stage.sv"
SYNTH_SCRIPT="${BASE}_synth.ys"

TIMING_CODE="${BASE}_assumptions_timing.sv"      # Cache timing constraints
CORE_SV="${BASE}_core.sv"                  # Modified core with cache timing

echo "=========================================="
echo "Ibex Synthesis with Instruction Constraints"
echo "=========================================="
echo "Input DSL:     $INPUT_DSL"
echo "Output folder: $OUTPUT_DIR"
echo "Output AIGER:  ${BASE}_post_abc.aig"
echo ""

# Determine total steps
if [ "$SYNTHESIZE_GATES" = true ]; then
    TOTAL_STEPS=4
else
    TOTAL_STEPS=3
fi

# Step 1: Generate assumptions code (inline, no module)
echo "[1/$TOTAL_STEPS] Generating instruction assumptions..."
pdat-dsl codegen "$INPUT_DSL" "$ASSUMPTIONS_CODE"

if [ $? -ne 0 ]; then
    echo "ERROR: Failed to generate assumptions"
    exit 1
fi

# Step 2: Inject assumptions into ibex_id_stage.sv
echo "[2/$TOTAL_STEPS] Injecting assumptions into ibex_id_stage.sv..."

# Find Ibex core path:
# 1. Use IBEX_ROOT environment variable if set
# 2. Try ../PdatCoreSim/cores/ibex
# 3. Try ../CoreSim/cores/ibex
# 4. Error if none found
if [ -z "$IBEX_ROOT" ]; then
    if [ -d "../PdatCoreSim/cores/ibex" ]; then
        IBEX_ROOT="../PdatCoreSim/cores/ibex"
    elif [ -d "../CoreSim/cores/ibex" ]; then
        IBEX_ROOT="../CoreSim/cores/ibex"
    else
        echo "ERROR: Could not find Ibex core directory. Tried:"
        echo "  - ../PdatCoreSim/cores/ibex"
        echo "  - ../CoreSim/cores/ibex"
        echo ""
        echo "Please set IBEX_ROOT environment variable or ensure Ibex is in one of these locations"
        exit 1
    fi
fi

echo "Using Ibex core: $IBEX_ROOT"

python3 scripts/inject_checker.py --assumptions-file "$ASSUMPTIONS_CODE" "$IBEX_ROOT/rtl/ibex_id_stage.sv" "$ID_STAGE_SV"

if [ $? -ne 0 ]; then
    echo "ERROR: Failed to inject ISA assumptions"
    exit 1
fi

# Step 2.5: Check if timing constraints were generated and inject into ibex_core.sv
CORE_MODIFIED_FLAG=""
if [ -f "$TIMING_CODE" ]; then
    echo "[2.5/$TOTAL_STEPS] Detected timing constraints, injecting into ibex_core.sv..."

    # Set Ibex root path early (needed for core injection)
    IBEX_ROOT="${IBEX_ROOT:-../CoreSim/cores/ibex}"

    python3 scripts/inject_core_timing.py \
        --timing-file "$TIMING_CODE" \
        "$IBEX_ROOT/rtl/ibex_core.sv" \
        "$CORE_SV"

    if [ $? -ne 0 ]; then
        echo "ERROR: Failed to inject timing constraints into ibex_core.sv"
        exit 1
    fi

    CORE_MODIFIED_FLAG="--core-modified $CORE_SV"
    echo "  Timing constraints injected successfully"
else
    echo "  No timing constraints detected (this is normal for ISA-only optimization)"
fi

# Step 3: Generate synthesis script
echo "[3/$TOTAL_STEPS] Generating synthesis script..."

if [ -n "$CONFIG_FILE" ]; then
    # Config mode
    echo "  Using config file: $CONFIG_FILE"

    # Build modified-files argument
    MODIFIED_FILES_ARGS="--modified-files id_stage_isa=${ID_STAGE_SV}"
    if [ -f "$CORE_SV" ]; then
        MODIFIED_FILES_ARGS="$MODIFIED_FILES_ARGS core_timing=${CORE_SV}"
    fi

    python3 scripts/make_synthesis_script.py \
        --config "$CONFIG_FILE" \
        $MODIFIED_FILES_ARGS \
        -o "$SYNTH_SCRIPT" \
        -a "${BASE}"
else
    # Legacy mode
    # Set Ibex root path if not already set
    IBEX_ROOT="${IBEX_ROOT:-../CoreSim/cores/ibex}"

    if [ "$WRITEBACK_STAGE" = true ]; then
        echo "  Enabling 3-stage pipeline (WritebackStage=1)"
        python3 scripts/make_synthesis_script.py "$ID_STAGE_SV" \
            -o "$SYNTH_SCRIPT" -a "${BASE}" --ibex-root "$IBEX_ROOT" --writeback-stage \
            $CORE_MODIFIED_FLAG
    else
        python3 scripts/make_synthesis_script.py "$ID_STAGE_SV" \
            -o "$SYNTH_SCRIPT" -a "${BASE}" --ibex-root "$IBEX_ROOT" \
            $CORE_MODIFIED_FLAG
    fi
fi

if [ $? -ne 0 ]; then
    echo "ERROR: Failed to generate synthesis script"
    exit 1
fi

# Step 4: Run synthesis
echo "[4/$TOTAL_STEPS] Running synthesis with Synlig (this may take several minutes)..."
YOSYS_LOG="${BASE}_yosys.log"

# Set unique Surelog cache directory to avoid conflicts with parallel runs
# Use PID to ensure uniqueness even when running in parallel
export SLPP_ALL="$OUTPUT_DIR/slpp_all_$$"
mkdir -p "$SLPP_ALL"

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
echo "  - $ASSUMPTIONS_CODE (ISA assumptions)"
echo "  - $ID_STAGE_SV (modified ibex_id_stage.sv)"
if [ -f "$TIMING_CODE" ]; then
    echo "  - $TIMING_CODE (cache timing constraints)"
    echo "  - $CORE_SV (modified ibex_core.sv)"
fi
echo "  - $SYNTH_SCRIPT (synthesis script)"
echo "  - ${BASE}_yosys.aig (AIGER from Yosys, before ABC)"
echo "  - $YOSYS_LOG (Yosys synthesis log)"
echo ""

# Step 5: Run external ABC if available
if command -v abc &> /dev/null; then
    ABC_INPUT="${BASE}_yosys.aig"
    ABC_OUTPUT="${BASE}_post_abc.aig"
    ABC_LOG="${BASE}_abc.log"

    if [ -f "$ABC_INPUT" ] && [ -s "$ABC_INPUT" ]; then
        echo "Running external ABC with sequential optimization (scorr)..."
        echo "Input:  $ABC_INPUT"
        echo "Output: $ABC_OUTPUT"
        echo ""

        echo "ABC k-induction depth: $ABC_DEPTH (should match pipeline depth)"
        # Two-stage optimization for best results:
        # 1. First optimize WITH constraints for maximum reduction
        # 2. Then extract clean outputs without constraints   

        # Get the number of real outputs (before constraints)
        ABC_STATS=$(abc -c "read_aiger $ABC_INPUT; print_stats" 2>&1 | grep "i/o")
        if echo "$ABC_STATS" | grep -q "(c="; then
            TOTAL_OUTPUTS=$(echo "$ABC_STATS" | sed -n 's/.*i\/o = *[0-9]*\/ *\([0-9]*\).*/\1/p')
            NUM_CONSTRAINTS=$(echo "$ABC_STATS" | sed -n 's/.*c=\([0-9]*\).*/\1/p')
            REAL_OUTPUTS=$((TOTAL_OUTPUTS - NUM_CONSTRAINTS))
            echo "Detected $NUM_CONSTRAINTS constraints, will extract $REAL_OUTPUTS real outputs"

            # Build constraint removal commands for ALL constraints
            CONSTRAINT_CMDS="constr -r;"
            # Remove each constraint output from highest index downward
            for ((i=TOTAL_OUTPUTS-1; i>=REAL_OUTPUTS; i--)); do
                CONSTRAINT_CMDS="$CONSTRAINT_CMDS removepo -N $i;"
            done
        else
            REAL_OUTPUTS=""
            NUM_CONSTRAINTS=0
            TOTAL_OUTPUTS=0
            echo "No constraints detected"
            # No constraint removal needed
            CONSTRAINT_CMDS=""
        fi

        # Single unified optimization flow
        # Always use -c -m flags (they work fine even without constraints)
        abc -c "read_aiger $ABC_INPUT; strash; cycle 100; scorr -c -m -F $ABC_DEPTH -C 30000 -S 20 -v; $CONSTRAINT_CMDS rewrite -l; fraig; balance -l; print_stats; write_aiger $ABC_OUTPUT" 2>&1 | tee "$ABC_LOG" | grep -E "^output|i/o =|lat =|and =|constraint|Removed equivs"

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
if [ -f "$TIMING_CODE" ]; then
    echo "The design has been synthesized with ISA + timing constraints."
    echo "Logic for outlawed instructions and impossible timing scenarios"
    echo "should be optimized away via assumptions and ABC optimization."
else
    echo "The design has been synthesized with ISA constraints."
    echo "Logic for outlawed instructions should be optimized away via"
    echo "assumptions and ABC optimization."
fi
