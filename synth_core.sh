#!/bin/bash
# End-to-end script: DSL file → Optimized RISC-V core with instruction constraints
#
# Supports multiple cores via YAML config files (Ibex, BOOM, Rocket, CVA6, etc.)
# Usage: ./synth_core.sh [OPTIONS] <rules.dsl> [output_dir]

set -e

# Parse arguments
SYNTHESIZE_GATES=false
ABC_DEPTH=2
WRITEBACK_STAGE=false
CONFIG_FILE=""
CORE_NAME="ibex"  # Default to ibex for this project
RUN_ODC_ANALYSIS=false
while [[ "$#" -gt 0 ]]; do
    case $1 in
        --gates) SYNTHESIZE_GATES=true; shift ;;
        --3stage) WRITEBACK_STAGE=true; ABC_DEPTH=3; shift ;;
        --abc-depth)
            ABC_DEPTH="$2"
            ABC_DEPTH_USER_SET=true
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
        --no-config)
            CORE_NAME=""  # Disable default, force legacy mode
            CONFIG_FILE=""
            shift
            ;;
        --odc-analysis) RUN_ODC_ANALYSIS=true; shift ;;
        -h|--help)
            echo "Usage: $0 [OPTIONS] <rules.dsl> [output_dir|output.il]"
            echo ""
            echo "Generates optimized RISC-V core with instruction constraints from DSL file"
            echo ""
            echo "Options:"
            echo "  --gates           Also synthesize to gate-level netlist with Skywater PDK"
            echo "  --3stage          Enable Ibex 3-stage pipeline (IF, ID/EX, WB) and set ABC depth=3"
            echo "  --abc-depth N     Set ABC k-induction depth (default: 2, matches 2-stage pipeline)"
            echo "  --config FILE     Use YAML config file (overrides --core default)"
            echo "  --core NAME       Core name for auto-config lookup (default: ibex, looks for configs/NAME.yaml)"
            echo "  --no-config       Disable config mode and use legacy hardcoded paths"
            echo "  --odc-analysis    Run complete ODC analysis on ALL fields (shamt, rd, rs1, rs2, imm)"
            echo "                    Automatically detects, verifies, and applies all ODC optimizations"
            echo ""
            echo "Arguments:"
            echo "  rules.dsl       DSL file with instruction constraints"
            echo "  output_dir      Base directory for outputs (default: output/)"
            echo "  output.il       Specific output file path (if ends with .il)"
            echo ""
            echo "Config Mode (DEFAULT):"
            echo "  Config mode is enabled by default (--core ibex). Source files and paths are"
            echo "  read from configs/ibex.yaml. Use --no-config to force legacy mode with"
            echo "  hardcoded paths. Config mode supports multiple cores (Ibex, BOOM, Rocket, etc.)"
            echo ""
            echo "Output organization:"
            echo "  - Files are organized in subfolders named after the DSL file"
            echo "  - e.g., my_rules.dsl → output/my_rules/<core>_optimized.il"
            echo "  - In legacy mode (no --config): ibex_optimized.il"
            echo "  - In config mode: <core_name>_optimized.il (e.g., boom_optimized.il)"
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
            echo "  $0 --odc-analysis my_rules.dsl          # Run ODC analysis after optimization"
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

# Determine output file prefix based on mode
if [ -n "$CONFIG_FILE" ]; then
    # Get core name, default ABC depth, clock name, and module name from config
    CONFIG_VALUES=$(python3 -c "
import sys
sys.path.insert(0, 'scripts')
try:
    from config_loader import ConfigLoader
    config = ConfigLoader.load_config('$CONFIG_FILE')
    core_name = config.core_name
    default_depth = config.synthesis.abc_config.get('default_depth', 2) if config.synthesis.abc_config else 2
    clk_name = config.signals.get('clk', 'clk_i') if hasattr(config, 'signals') and config.signals else 'clk_i'
    top_module = config.synthesis.top_module if hasattr(config.synthesis, 'top_module') else 'ibex_core'
    print(f'{core_name}_optimized')
    print(default_depth)
    print(clk_name)
    print(top_module)
except Exception as e:
    print('core_optimized')
    print('2')
    print('clk_i')
    print('ibex_core')
")
    OUTPUT_PREFIX=$(echo "$CONFIG_VALUES" | sed -n '1p')
    CONFIG_DEFAULT_DEPTH=$(echo "$CONFIG_VALUES" | sed -n '2p')
    CLK_NAME=$(echo "$CONFIG_VALUES" | sed -n '3p')
    MODULE_NAME=$(echo "$CONFIG_VALUES" | sed -n '4p')

    # Override ABC_DEPTH with config default if not explicitly set via --abc-depth
    # Check if ABC_DEPTH is still at default value (2) - if so, use config default
    if [ "$ABC_DEPTH" -eq 2 ] && [ -z "$ABC_DEPTH_USER_SET" ]; then
        ABC_DEPTH=$CONFIG_DEFAULT_DEPTH
        echo "  Using ABC depth from config: $ABC_DEPTH"
    fi
else
    # Legacy mode: use ibex prefix, default clock name, and default module
    OUTPUT_PREFIX="ibex_optimized"
    CLK_NAME="clk_i"
    MODULE_NAME="ibex_core"
fi

# Handle output argument:
# - If not provided: output/<dsl_name>/<prefix>.il
# - If ends with .il: use as full path
# - Otherwise: treat as directory and use <dsl_name>/<prefix>.il
if [ -z "$2" ]; then
    OUTPUT_DIR="output/$DSL_BASENAME"
    OUTPUT_IL="$OUTPUT_DIR/${OUTPUT_PREFIX}.il"
elif [[ "$2" == *.il ]]; then
    OUTPUT_IL="$2"
    OUTPUT_DIR=$(dirname "$OUTPUT_IL")
else
    OUTPUT_DIR="$2/$DSL_BASENAME"
    OUTPUT_IL="$OUTPUT_DIR/${OUTPUT_PREFIX}.il"
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
if [ -n "$CONFIG_FILE" ]; then
    CORE_DISPLAY=$(python3 -c "
import sys
sys.path.insert(0, 'scripts')
try:
    from config_loader import ConfigLoader
    config = ConfigLoader.load_config('$CONFIG_FILE')
    print(config.core_name.upper())
except:
    print('Core')
" 2>/dev/null)
    echo "$CORE_DISPLAY Synthesis with Instruction Constraints"
else
    echo "Ibex Synthesis with Instruction Constraints"
fi
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

# Pass config file to codegen if in config mode (for signal name mappings)
if [ -n "$CONFIG_FILE" ]; then
    # pdat-dsl needs config from PdatRiscvDsl/configs/, not PdatScorr/configs/
    # Try to find corresponding config in PdatRiscvDsl
    DSL_CONFIG="../PdatRiscvDsl/configs/$(basename "$CONFIG_FILE")"
    if [ -f "$DSL_CONFIG" ]; then
        pdat-dsl codegen --config "$DSL_CONFIG" "$INPUT_DSL" "$ASSUMPTIONS_CODE"
    else
        echo "  Warning: DSL config not found at $DSL_CONFIG, generating without config"
        pdat-dsl codegen "$INPUT_DSL" "$ASSUMPTIONS_CODE"
    fi
else
    pdat-dsl codegen "$INPUT_DSL" "$ASSUMPTIONS_CODE"
fi

if [ $? -ne 0 ]; then
    echo "ERROR: Failed to generate assumptions"
    exit 1
fi

# Step 2: Inject assumptions into ID stage
echo "[2/$TOTAL_STEPS] Injecting assumptions into ID stage..."

# Determine core root path based on mode
if [ -n "$CONFIG_FILE" ]; then
    # Config mode: Validate config file exists first
    if [ ! -f "$CONFIG_FILE" ]; then
        echo "ERROR: Config file not found: $CONFIG_FILE"
        exit 1
    fi

    # Get core root from config file
    CORE_ROOT=$(python3 -c "
import sys
sys.path.insert(0, 'scripts')
try:
    from config_loader import ConfigLoader
    config = ConfigLoader.load_config('$CONFIG_FILE')
    print(config.synthesis.core_root_resolved)
except Exception as e:
    print(f'ERROR: {e}', file=sys.stderr)
    sys.exit(1)
")

    if [ $? -ne 0 ] || [ -z "$CORE_ROOT" ] || [[ "$CORE_ROOT" == ERROR:* ]]; then
        echo "ERROR: Failed to load core root from config file"
        echo "$CORE_ROOT"
        exit 1
    fi

    # Get ID stage source file from config
    ID_STAGE_SOURCE=$(python3 -c "
import sys
sys.path.insert(0, 'scripts')
try:
    from config_loader import ConfigLoader
    config = ConfigLoader.load_config('$CONFIG_FILE')
    inj = config.get_injection('isa')
    if inj:
        print(f'{config.synthesis.core_root_resolved}/{inj.source_file}')
    else:
        print('ERROR: No ISA injection point found', file=sys.stderr)
        sys.exit(1)
except Exception as e:
    print(f'ERROR: {e}', file=sys.stderr)
    sys.exit(1)
")

    if [ $? -ne 0 ] || [ -z "$ID_STAGE_SOURCE" ] || [[ "$ID_STAGE_SOURCE" == ERROR:* ]]; then
        echo "ERROR: Could not find ISA injection point in config"
        echo "$ID_STAGE_SOURCE"
        exit 1
    fi
else
    # Legacy mode: Use IBEX_ROOT
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

    CORE_ROOT="$IBEX_ROOT"
    ID_STAGE_SOURCE="$IBEX_ROOT/rtl/ibex_id_stage.sv"
fi

echo "Using core root: $CORE_ROOT"

python3 scripts/inject_checker.py --assumptions-file "$ASSUMPTIONS_CODE" "$ID_STAGE_SOURCE" "$ID_STAGE_SV"

if [ $? -ne 0 ]; then
    echo "ERROR: Failed to inject ISA assumptions"
    exit 1
fi

# Step 2.5: Check if timing constraints were generated and inject into core
CORE_MODIFIED_FLAG=""
if [ -f "$TIMING_CODE" ]; then
    echo "[2.5/$TOTAL_STEPS] Detected timing constraints, injecting into core..."

    if [ -n "$CONFIG_FILE" ]; then
        # Config mode: Get core source file from config
        CORE_SOURCE=$(python3 -c "
import sys
sys.path.insert(0, 'scripts')
try:
    from config_loader import ConfigLoader
    config = ConfigLoader.load_config('$CONFIG_FILE')
    inj = config.get_injection('timing')
    if inj:
        print(f'{config.synthesis.core_root_resolved}/{inj.source_file}')
    else:
        print('ERROR: No timing injection point found', file=sys.stderr)
        sys.exit(1)
except Exception as e:
    print(f'ERROR: {e}', file=sys.stderr)
    sys.exit(1)
")

        if [ $? -ne 0 ] || [ -z "$CORE_SOURCE" ] || [[ "$CORE_SOURCE" == ERROR:* ]]; then
            echo "ERROR: Could not find timing injection point in config"
            echo "$CORE_SOURCE"
            exit 1
        fi
    else
        # Legacy mode
        CORE_SOURCE="$CORE_ROOT/rtl/ibex_core.sv"
    fi

    python3 scripts/inject_core_timing.py \
        --timing-file "$TIMING_CODE" \
        "$CORE_SOURCE" \
        "$CORE_SV"

    if [ $? -ne 0 ]; then
        echo "ERROR: Failed to inject timing constraints"
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

    # Check for ODC-optimized register file
    RF_OPT="${OUTPUT_DIR}/odc_optimized_rtl/ibex_register_file_ff_optimized.sv"
    if [ -f "$RF_OPT" ]; then
        echo "  Found ODC-optimized register file: $RF_OPT"
        MODIFIED_FILES_ARGS="$MODIFIED_FILES_ARGS register_file_opt=${RF_OPT}"
    fi

    # Build writeback-stage flag if needed
    WRITEBACK_FLAG=""
    if [ "$WRITEBACK_STAGE" = true ]; then
        echo "  Enabling 3-stage pipeline (WritebackStage=1)"
        WRITEBACK_FLAG="--writeback-stage"
    fi

    python3 scripts/make_synthesis_script.py \
        --config "$CONFIG_FILE" \
        $MODIFIED_FILES_ARGS \
        $WRITEBACK_FLAG \
        -o "$SYNTH_SCRIPT" \
        -a "${BASE}"
else
    # Legacy mode
    if [ "$WRITEBACK_STAGE" = true ]; then
        echo "  Enabling 3-stage pipeline (WritebackStage=1)"
        python3 scripts/make_synthesis_script.py "$ID_STAGE_SV" \
            -o "$SYNTH_SCRIPT" -a "${BASE}" --ibex-root "$CORE_ROOT" --writeback-stage \
            $CORE_MODIFIED_FLAG
    else
        python3 scripts/make_synthesis_script.py "$ID_STAGE_SV" \
            -o "$SYNTH_SCRIPT" -a "${BASE}" --ibex-root "$CORE_ROOT" \
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
# Use PID + random to ensure uniqueness even in nested parallel execution
# (e.g., batch_synth.sh running multiple jobs in parallel)
export SLPP_ALL="$OUTPUT_DIR/slpp_all_$$_$RANDOM"
mkdir -p "$SLPP_ALL"

# Run Synlig from OUTPUT_DIR to ensure slpp_all is created there, not in current directory
# This prevents race conditions when running multiple synthesis jobs in parallel
(cd "$OUTPUT_DIR" && synlig -s "$(basename "$SYNTH_SCRIPT")") 2>&1 | tee "$YOSYS_LOG"

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
        abc -c "read_aiger $ABC_INPUT; strash; cycle 100; scorr -c -m -F $ABC_DEPTH -C 30000 -S 20 -v; $CONSTRAINT_CMDS rewrite -l; balance -l; print_stats; write_aiger $ABC_OUTPUT" 2>&1 | tee "$ABC_LOG" | grep -E "^output|i/o =|lat =|and =|constraint|Removed equivs"

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

# Step 5.5 (optional): ODC Analysis
if [ "$RUN_ODC_ANALYSIS" = true ]; then
    # If we're doing ODC analysis with gate synthesis, synthesize baseline to gates first
    # so we have something to compare against
    if [ "$SYNTHESIZE_GATES" = true ] && [ ! -f "$OUTPUT_DIR/${OUTPUT_PREFIX}_gates.log" ]; then
        echo "Synthesizing baseline to gates before ODC analysis (for comparison)..."
        ./scripts/synth_to_gates.sh "$BASE" "" "$CLK_NAME" "$MODULE_NAME"
        echo ""
    fi

    echo "=========================================="
    echo "ODC Analysis (Error Injection + Bounded SEC)"
    echo "=========================================="
    echo ""

    # Determine which config file to use
    if [ -n "$CONFIG_FILE" ]; then
        ODC_CONFIG="$CONFIG_FILE"
    else
        # Legacy mode - use default ibex config
        ODC_CONFIG="configs/ibex.yaml"
    fi

    # Determine baseline AIGER file
    # Use Yosys output (NOT ABC-optimized) to ensure both circuits have same structure
    # ABC optimization removes constraints which causes miter issues
    if [ -f "${BASE}_yosys.aig" ]; then
        BASELINE_AIG="${BASE}_yosys.aig"
        echo "Using Yosys-generated circuit as baseline: $BASELINE_AIG"
    else
        echo "ERROR: No Yosys AIGER file found for baseline. Cannot run ODC analysis."
        RUN_ODC_ANALYSIS=false
    fi

    if [ "$RUN_ODC_ANALYSIS" = true ]; then
        ODC_OUTPUT_DIR="$OUTPUT_DIR/odc_analysis"

        echo "Running ODC analysis with k=$ABC_DEPTH..."
        echo "  DSL: $INPUT_DSL"
        echo "  Baseline: $BASELINE_AIG"
        echo "  Config: $ODC_CONFIG"
        echo "  Output: $ODC_OUTPUT_DIR"
        echo ""

        python3 scripts/odc_analysis.py "$INPUT_DSL" \
            --baseline-aig "$BASELINE_AIG" \
            --output-dir "$ODC_OUTPUT_DIR" \
            --k-depth "$ABC_DEPTH" \
            --config "$ODC_CONFIG" \
            --scope all

        if [ $? -eq 0 ]; then
            echo ""
            echo "ODC analysis complete!"
            echo "  Reports: $ODC_OUTPUT_DIR/odc_report.{json,md}"
            echo ""

            # Check if any ODCs were found (bit-level or mux-level)
            ODC_REPORT="$ODC_OUTPUT_DIR/odc_report.json"
            MUX_ODC_REPORT="$ODC_OUTPUT_DIR/mux_odc_analysis.json"

            ODC_COUNT=$(python3 -c "
import json
count = 0
try:
    with open('$ODC_REPORT') as f:
        report = json.load(f)
    count = report.get('metadata', {}).get('confirmed_odcs', 0)
except:
    pass
print(count)
" 2>/dev/null || echo "0")

            MUX_ODC_COUNT=$(python3 -c "
import json
count = 0
try:
    with open('$MUX_ODC_REPORT') as f:
        report = json.load(f)
    count = len([c for c in report.get('unreachable_mux_cases', []) if c.get('sec_verified', False)])
except:
    pass
print(count)
" 2>/dev/null || echo "0")

            TOTAL_ODC_COUNT=$((ODC_COUNT + MUX_ODC_COUNT))

            if [ "$TOTAL_ODC_COUNT" -gt 0 ]; then
                echo "Found $ODC_COUNT bit-level ODCs and $MUX_ODC_COUNT mux-level ODCs - applying optimizations..."
                echo ""

                # Apply ODC optimizations
                OPTIMIZED_RTL_DIR="$OUTPUT_DIR/odc_optimized_rtl"
                OPTIMIZED_SYNTH_DIR="$OUTPUT_DIR/odc_optimized_synthesis"

                # Apply bit-level optimizations (if any)
                if [ "$ODC_COUNT" -gt 0 ]; then
                    echo "Applying bit-level ODC optimizations..."
                    python3 scripts/apply_odc_optimizations.py "$ODC_REPORT" \
                        --rtl-dir "$CORE_ROOT/rtl" \
                        --output-dir "$OPTIMIZED_RTL_DIR" \
                        --config "$ODC_CONFIG"
                fi

                # Apply mux-level optimizations (if any)
                if [ "$MUX_ODC_COUNT" -gt 0 ]; then
                    echo "Applying mux-level ODC optimizations..."
                    # If bit-level already ran, use its output as input; otherwise use original
                    if [ -f "$OPTIMIZED_RTL_DIR/ibex_alu_optimized.sv" ]; then
                        INPUT_ALU="$OPTIMIZED_RTL_DIR/ibex_alu_optimized.sv"
                    else
                        INPUT_ALU="$CORE_ROOT/rtl/ibex_alu.sv"
                        mkdir -p "$OPTIMIZED_RTL_DIR"
                    fi

                    python3 scripts/apply_mux_optimizations.py "$MUX_ODC_REPORT" \
                        --config "$ODC_CONFIG" \
                        --output-dir "$OPTIMIZED_RTL_DIR"

                    # The output is ibex_alu_mux_optimized.sv, rename to ibex_alu_optimized.sv
                    if [ -f "$OPTIMIZED_RTL_DIR/ibex_alu_mux_optimized.sv" ]; then
                        mv "$OPTIMIZED_RTL_DIR/ibex_alu_mux_optimized.sv" "$OPTIMIZED_RTL_DIR/ibex_alu_optimized.sv"
                    fi
                fi

                # Check if we have optimized RTL files (discover dynamically)
                OPTIMIZED_FILES=$(ls "$OPTIMIZED_RTL_DIR"/*_optimized.sv 2>/dev/null || true)

                if [ -n "$OPTIMIZED_FILES" ]; then
                    # Copy all optimized RTL to synthesis directory
                    mkdir -p "$OPTIMIZED_SYNTH_DIR"

                    echo "Found optimized RTL files:"
                    for opt_file in $OPTIMIZED_FILES; do
                        cp "$opt_file" "$OPTIMIZED_SYNTH_DIR/"
                        filename=$(basename $opt_file)
                        echo "  - $filename"

                        # Track what type of optimization this is
                        if [[ "$filename" == *"register_file"* ]]; then
                            echo "    (Register file optimization - eliminates unused register storage)"
                        elif [[ "$filename" == *"alu"* ]]; then
                            echo "    (ALU optimization - eliminates unused functional units)"
                        elif [[ "$filename" == *"id_stage"* ]]; then
                            echo "    (ID stage optimization - may include multiple optimizations)"
                        fi
                    done

                    echo "Re-synthesizing with ODC optimizations..."

                    # Determine which optimized file to use as primary for synthesis
                    # Priority: register_file > ALU > ID stage
                    # (Register file is most fundamental - all others can use it)
                    OPTIMIZED_RTL_FILE=""

                    # Check for optimized register file (highest priority - eliminates storage)
                    REGFILE_OPT=$(ls "$OPTIMIZED_SYNTH_DIR"/*register_file*_optimized.sv 2>/dev/null | head -1)
                    if [ -n "$REGFILE_OPT" ]; then
                        OPTIMIZED_RTL_FILE=$(basename "$REGFILE_OPT")
                        echo "  Primary: $OPTIMIZED_RTL_FILE (register file - eliminates unused storage)"
                    else
                        # Check for ALU optimization
                        ALU_OPT=$(ls "$OPTIMIZED_SYNTH_DIR"/*alu*_optimized.sv 2>/dev/null | head -1)
                        if [ -n "$ALU_OPT" ]; then
                            OPTIMIZED_RTL_FILE=$(basename "$ALU_OPT")
                            echo "  Primary: $OPTIMIZED_RTL_FILE (ALU optimization)"
                        else
                            # Fallback to ID stage or any optimized file
                            ANY_OPT=$(ls "$OPTIMIZED_SYNTH_DIR"/*_optimized.sv 2>/dev/null | head -1)
                            if [ -n "$ANY_OPT" ]; then
                                OPTIMIZED_RTL_FILE=$(basename "$ANY_OPT")
                                echo "  Primary: $OPTIMIZED_RTL_FILE"
                            fi
                        fi
                    fi

                    if [ -z "$OPTIMIZED_RTL_FILE" ]; then
                        echo "  ERROR: No optimized RTL file found in $OPTIMIZED_SYNTH_DIR"
                        exit 1
                    fi

                    # Synthesize optimized version
                    python3 << PYEOF
import sys
from pathlib import Path
sys.path.insert(0, 'odc')
from synthesis import synthesize_error_injected_circuit

result = synthesize_error_injected_circuit(
    error_injected_rtl=Path('$OPTIMIZED_SYNTH_DIR/$OPTIMIZED_RTL_FILE'),
    dsl_file=Path('$INPUT_DSL'),
    output_dir=Path('$OPTIMIZED_SYNTH_DIR'),
    config_file=Path('$ODC_CONFIG'),
    k_depth=$ABC_DEPTH
)
sys.exit(0 if result else 1)
PYEOF

                    ODC_SYNTH_EXIT=$?
                    if [ $ODC_SYNTH_EXIT -eq 0 ]; then
                        # Run ABC optimization on optimized circuit
                        # Use the base name from the optimized RTL file
                        OPTIMIZED_BASE="${OPTIMIZED_RTL_FILE%.sv}"
                        OPTIMIZED_YOSYS_AIG="$OPTIMIZED_SYNTH_DIR/${OPTIMIZED_BASE}_yosys.aig"
                        OPTIMIZED_ABC_AIG="$OPTIMIZED_SYNTH_DIR/${OPTIMIZED_BASE}_post_abc.aig"

                        # Get constraint info
                        ABC_STATS_OPT=$(abc -c "read_aiger $OPTIMIZED_YOSYS_AIG; print_stats" 2>&1 | grep "i/o")

                        if echo "$ABC_STATS_OPT" | grep -q "(c="; then
                            TOTAL_OUTPUTS=$(echo "$ABC_STATS_OPT" | grep -oP 'i/o\s*=\s*\d+/\s*\K\d+')
                            CONSTR_COUNT=$(echo "$ABC_STATS_OPT" | grep -oP '\(c=\K\d+')
                            REAL_OUTPUTS=$((TOTAL_OUTPUTS - CONSTR_COUNT))

                            CONSTRAINT_CMDS="constr -r;"
                            for ((i=TOTAL_OUTPUTS-1; i>=REAL_OUTPUTS; i--)); do
                                CONSTRAINT_CMDS="$CONSTRAINT_CMDS removepo -N $i;"
                            done
                        else
                            CONSTRAINT_CMDS=""
                        fi

                        abc -c "
                            read_aiger $OPTIMIZED_YOSYS_AIG;
                            strash;
                            cycle 100;
                            scorr -c -m -F $ABC_DEPTH -C 30000 -S 20 -v;
                            $CONSTRAINT_CMDS
                            rewrite -l;
                            fraig;
                            balance -l;
                            print_stats;
                            write_aiger $OPTIMIZED_ABC_AIG;
                        " > "$OPTIMIZED_SYNTH_DIR/abc.log" 2>&1

                        # Compare results
                        BASELINE_STATS=$(abc -c "read_aiger $ABC_OUTPUT; print_stats" 2>&1 | grep "i/o =")
                        OPTIMIZED_STATS=$(abc -c "read_aiger $OPTIMIZED_ABC_AIG; print_stats" 2>&1 | grep "i/o =")

                        BASELINE_AND=$(echo "$BASELINE_STATS" | grep -oP 'and\s*=\s*\K\d+')
                        OPTIMIZED_AND=$(echo "$OPTIMIZED_STATS" | grep -oP 'and\s*=\s*\K\d+')

                        if [ -n "$BASELINE_AND" ] && [ -n "$OPTIMIZED_AND" ]; then
                            REDUCTION=$((BASELINE_AND - OPTIMIZED_AND))
                            PERCENT=$(python3 -c "print(f'{100.0 * $REDUCTION / $BASELINE_AND:.2f}')")

                            echo ""
                            echo "ODC Optimization Results:"
                            echo "  Baseline:  $BASELINE_AND AND gates"
                            echo "  Optimized: $OPTIMIZED_AND AND gates"
                            echo "  Reduction: $REDUCTION gates ($PERCENT%)"

                            if [ "$REDUCTION" -gt 0 ]; then
                                echo "  ✓ ODC optimization successful!"
                            fi

                            # Run gate-level synthesis on ODC-optimized circuit if requested
                            if [ "$SYNTHESIZE_GATES" = true ]; then
                                echo ""
                                echo "Synthesizing ODC-optimized circuit to gate level..."
                                # Use the correct base name (already computed earlier)
                                OPTIMIZED_BASE_PATH="$OPTIMIZED_SYNTH_DIR/$OPTIMIZED_BASE"
                                ./scripts/synth_to_gates.sh "$OPTIMIZED_BASE_PATH" "" "$CLK_NAME" "$MODULE_NAME"

                                if [ $? -eq 0 ]; then
                                    # Extract and show chip area comparison
                                    # Format: "Chip area for module 'name': 39250.144000"
                                    BASELINE_AREA=$(grep "Chip area for module" "$OUTPUT_DIR/${OUTPUT_PREFIX}_gates.log" 2>/dev/null | tail -1 | awk '{print $NF}')
                                    OPTIMIZED_AREA=$(grep "Chip area for module" "$OPTIMIZED_SYNTH_DIR/${OPTIMIZED_BASE}_gates.log" 2>/dev/null | tail -1 | awk '{print $NF}')

                                    if [ -n "$BASELINE_AREA" ] && [ -n "$OPTIMIZED_AREA" ]; then
                                        AREA_REDUCTION=$(python3 -c "print(f'{float(${BASELINE_AREA:-0}) - float(${OPTIMIZED_AREA:-0}):.2f}')")
                                        AREA_PERCENT=$(python3 -c "print(f'{100.0 * (float(${BASELINE_AREA:-0}) - float(${OPTIMIZED_AREA:-0})) / float(${BASELINE_AREA:-1}):.2f}')")

                                        echo ""
                                        echo "Chip Area Comparison:"
                                        echo "  Baseline:  $BASELINE_AREA µm²"
                                        echo "  Optimized: $OPTIMIZED_AREA µm²"
                                        echo "  Reduction: $AREA_REDUCTION µm² ($AREA_PERCENT%)"
                                    fi


                                    # Compare timing if metrics are available
                                    BASELINE_TIMING="${BASE}_timing_metrics.json"
                                    OPTIMIZED_TIMING="${OPTIMIZED_BASE_PATH}_timing_metrics.json"

                                    if [ -f "$BASELINE_TIMING" ] && [ -f "$OPTIMIZED_TIMING" ]; then
                                        BASELINE_FREQ=$(python3 -c "import json; print(json.load(open('$BASELINE_TIMING')).get('max_frequency_mhz', 'N/A'))" 2>/dev/null || echo "N/A")
                                        OPTIMIZED_FREQ=$(python3 -c "import json; print(json.load(open('$OPTIMIZED_TIMING')).get('max_frequency_mhz', 'N/A'))" 2>/dev/null || echo "N/A")

                                        if [ "$BASELINE_FREQ" != "N/A" ] && [ "$OPTIMIZED_FREQ" != "N/A" ]; then
                                            FREQ_CHANGE=$(python3 -c "print(f'{float(${OPTIMIZED_FREQ:-0}) - float(${BASELINE_FREQ:-0}):.2f}')")
                                            FREQ_PERCENT=$(python3 -c "print(f'{100.0 * (float(${OPTIMIZED_FREQ:-0}) - float(${BASELINE_FREQ:-0})) / float(${BASELINE_FREQ:-1}):.2f}')")

                                            echo ""
                                            echo "Timing Comparison (10ns target period):"
                                            echo "  Baseline:  $BASELINE_FREQ MHz"
                                            echo "  Optimized: $OPTIMIZED_FREQ MHz"
                                            echo "  Change:    $FREQ_CHANGE MHz ($FREQ_PERCENT%)"
                                        fi

                                    fi
                                fi
                            fi
                        fi
                    else
                        echo ""
                        echo "ERROR: ODC-optimized synthesis failed"
                        echo "  Check log: $OPTIMIZED_SYNTH_DIR/${OPTIMIZED_RTL_FILE%.sv}_synlig.log"
                        echo ""
                        exit 1
                    fi
                fi
            fi
        else
            echo ""
            echo "WARNING: ODC analysis failed or incomplete"
            echo ""
        fi
    fi
fi

# Step 6 (optional): Gate-level synthesis (baseline only if ODC didn't run)
if [ "$SYNTHESIZE_GATES" = true ]; then
    # Check if ODC optimization already ran gate synthesis
    # Check for any optimized gates log (use wildcard to match any core)
    OPTIMIZED_GATES_LOG=$(ls "$OUTPUT_DIR/odc_optimized_synthesis/"*"_optimized_gates.log" 2>/dev/null | head -1)
    if [ -z "$OPTIMIZED_GATES_LOG" ]; then
        echo "Synthesizing to gate level with Skywater PDK..."
        ./scripts/synth_to_gates.sh "$BASE" "" "$CLK_NAME" "$MODULE_NAME"
    else
        echo ""
        echo "Gate synthesis already completed during ODC optimization"
        echo "(ODC-optimized gates in output/baseline/odc_optimized_synthesis/)"
    fi

    if [ $? -ne 0 ]; then
        echo "ERROR: Gate-level synthesis failed"
        exit 1
    fi
else
    echo "To synthesize to gates, run:"
    echo "  ./scripts/synth_to_gates.sh $BASE \"\" \"$CLK_NAME\" \"$MODULE_NAME\""
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
