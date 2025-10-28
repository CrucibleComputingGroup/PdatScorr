#!/bin/bash
# Synthesis with cache-aware timing constraints
# Injects into ibex_core.sv instead of ibex_id_stage.sv for full signal visibility

set -e

# Parse arguments (EXACTLY same as original)
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
            echo "Generates optimized Ibex core with ISA + timing constraints"
            echo ""
            echo "Options:"
            echo "  --gates           Also synthesize to gate-level netlist with Skywater PDK"
            echo "  --3stage          Enable Ibex 3-stage pipeline (IF, ID/EX, WB) and set ABC depth=3"
            echo "  --abc-depth N     Set ABC k-induction depth (default: 2, matches 2-stage pipeline)"
            echo ""
            echo "Arguments:"
            echo "  rules.dsl       DSL file with instruction constraints"
            echo "  output_dir      Base directory for outputs (default: output/)"
            echo "  output.il       Specific output file path (if ends with .il)"
            echo ""
            exit 0
            ;;
        *) break ;;
    esac
done

# Check DSL file exists (same as original)
if [ "$#" -lt 1 ]; then
    echo "ERROR: Missing required argument <rules.dsl>"
    echo "Run with --help for usage information"
    exit 1
fi

if [ ! -f "$1" ]; then
    echo "ERROR: DSL file '$1' not found"
    exit 1
fi

INPUT_DSL="$1"
DSL_BASENAME=$(basename "$INPUT_DSL" .dsl)

# Handle output argument (same as original)
if [ -z "$2" ]; then
    OUTPUT_DIR="output/${DSL_BASENAME}_timing"
    OUTPUT_IL="$OUTPUT_DIR/ibex_optimized.il"
elif [[ "$2" == *.il ]]; then
    OUTPUT_IL="$2"
    OUTPUT_DIR=$(dirname "$OUTPUT_IL")
else
    OUTPUT_DIR="$2/${DSL_BASENAME}_timing"
    OUTPUT_IL="$OUTPUT_DIR/ibex_optimized.il"
fi

# Ensure output directory exists
mkdir -p "$OUTPUT_DIR"

# Derive intermediate filenames
BASE="${OUTPUT_IL%.il}"
ASSUMPTIONS_CODE="${BASE}_assumptions.sv"  # ISA constraints
TIMING_CODE="${BASE}_cache_timing.sv"      # Cache timing constraints
ID_STAGE_SV="${BASE}_id_stage.sv"          # Modified id_stage with ISA
CORE_SV="${BASE}_core.sv"                  # Modified core with cache timing
SYNTH_SCRIPT="${BASE}_synth.ys"

echo "=========================================="
echo "Ibex Synthesis with ISA + Timing Constraints"
echo "=========================================="
echo "Input DSL:     $INPUT_DSL"
echo "Output folder: $OUTPUT_DIR"
echo "Output AIGER:  ${BASE}_post_abc.aig"
echo ""

# Determine total steps
if [ "$SYNTHESIZE_GATES" = true ]; then
    TOTAL_STEPS=5
else
    TOTAL_STEPS=4
fi

# Step 1: Generate ISA assumptions from DSL (same as original)
echo "[1/$TOTAL_STEPS] Generating ISA assumptions..."
pdat-dsl codegen --inline "$INPUT_DSL" "$ASSUMPTIONS_CODE"

if [ $? -ne 0 ]; then
    echo "ERROR: Failed to generate assumptions"
    exit 1
fi

# Step 2: Generate cache-aware timing constraints (NEW - separate file)
echo "[2/$TOTAL_STEPS] Generating cache-aware timing constraints..."
cat > "$TIMING_CODE" << 'EOF'

  // ========================================
  // Cache-Aware Timing Constraints
  // ========================================
  // Models realistic cache hit/miss behavior for ABC optimization
  // Injected at ibex_core level for full signal visibility

  // Instruction cache timing tracking
  logic [2:0] instr_stall_counter_q;
  logic instr_likely_miss;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      instr_stall_counter_q <= 3'b0;
      instr_likely_miss <= 1'b0;
    end else begin
      if (instr_req_o && !instr_gnt_i) begin
        instr_stall_counter_q <= instr_stall_counter_q + 1;
        // After 1 cycle of stalling, assume cache miss
        instr_likely_miss <= (instr_stall_counter_q >= 1);
      end else begin
        instr_stall_counter_q <= 3'b0;
        instr_likely_miss <= 1'b0;
      end

    end
  end

  // Data cache timing tracking
  logic [2:0] data_stall_counter_q;
  logic data_likely_miss;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      data_stall_counter_q <= 3'b0;
      data_likely_miss <= 1'b0;
    end else begin
      if (data_req_out && !data_gnt_i) begin
        data_stall_counter_q <= data_stall_counter_q + 1;
        data_likely_miss <= (data_stall_counter_q >= 1);
      end else if (data_rvalid_i) begin
        data_stall_counter_q <= 3'b0;
        data_likely_miss <= 1'b0;
      end

    end
  end

  // Cache-aware timing assumptions
  always_comb begin
    if (rst_ni) begin
      // Instruction cache: different bounds for hit vs miss
      if (!instr_likely_miss) begin
        assume(instr_stall_counter_q <= 3'd1);  // Cache hit: 1 cycle max
      end else begin
        assume(instr_stall_counter_q <= 3'd5);  // Cache miss: up to 5 cycles
      end

      // Data cache: different bounds for hit vs miss
      if (!data_likely_miss) begin
        assume(data_stall_counter_q <= 3'd1);   // Cache hit: 1 cycle max
      end else begin
        assume(data_stall_counter_q <= 3'd4);   // Cache miss: up to 4 cycles
      end

      // Force completion at maximum latency
      if (instr_stall_counter_q == 3'd5) begin
        assume(instr_gnt_i);  // Must grant at max stall
      end

      if (data_stall_counter_q == 3'd4) begin
        assume(data_gnt_i);  // Must grant at max stall
      end
    end
  end

EOF

echo "Generated cache timing constraints"

# Step 3a: Inject ISA constraints into ibex_id_stage.sv (same as original)
echo "[3a/$TOTAL_STEPS] Injecting ISA constraints into ibex_id_stage.sv..."
python3 scripts/inject_checker.py --assumptions-file "$ASSUMPTIONS_CODE" ../CoreSim/cores/ibex/rtl/ibex_id_stage.sv "$ID_STAGE_SV"

if [ $? -ne 0 ]; then
    # Try alternative path
    python3 scripts/inject_checker.py --assumptions-file "$ASSUMPTIONS_CODE" ../ibex/rtl/ibex_id_stage.sv "$ID_STAGE_SV"
    if [ $? -ne 0 ]; then
        echo "ERROR: Failed to inject ISA constraints"
        exit 1
    fi
fi

echo "Successfully injected ISA constraints into ibex_id_stage.sv"

# Step 3b: Inject cache timing constraints into ibex_core.sv (NEW)
echo "[3b/$TOTAL_STEPS] Injecting cache timing constraints into ibex_core.sv..."

# Find ibex_core.sv
IBEX_CORE_ORIG="../CoreSim/cores/ibex/rtl/ibex_core.sv"
if [ ! -f "$IBEX_CORE_ORIG" ]; then
    IBEX_CORE_ORIG="../ibex/rtl/ibex_core.sv"
fi

if [ ! -f "$IBEX_CORE_ORIG" ]; then
    echo "ERROR: Cannot find ibex_core.sv"
    exit 1
fi

# Inject cache timing constraints before load_store_unit instantiation
awk -v timing="$(cat "$TIMING_CODE")" '
  /ibex_load_store_unit #\(/ {
    print ""
    print "  // Injected Cache Timing Constraints"
    print timing
    print ""
  }
  { print }
' "$IBEX_CORE_ORIG" > "$CORE_SV"

if [ ! -f "$CORE_SV" ] || [ ! -s "$CORE_SV" ]; then
    echo "ERROR: Failed to inject cache timing constraints"
    exit 1
fi

echo "Successfully injected cache timing constraints into ibex_core.sv"

# Step 4: Generate synthesis script (same as original)
echo "[4/$TOTAL_STEPS] Generating synthesis script..."

IBEX_ROOT="${IBEX_ROOT:-../CoreSim/cores/ibex}"
if [ ! -d "$IBEX_ROOT/rtl" ]; then
    IBEX_ROOT="../ibex"
fi

# Generate custom Yosys script (can't use make_synthesis_script.py - it's for id_stage injection)
cat > "$SYNTH_SCRIPT" << EOFSYNTH
# Synlig script for Ibex with cache-aware timing in ibex_core.sv
# Ibex path: $IBEX_ROOT

verilog_defaults -add -I$IBEX_ROOT/rtl
verilog_defaults -add -I$IBEX_ROOT/shared/rtl
verilog_defaults -add -I$IBEX_ROOT/vendor/lowrisc_ip/ip/prim/rtl
verilog_defaults -add -I$IBEX_ROOT/vendor/lowrisc_ip/dv/sv/dv_utils

read_systemverilog \\
  -I$IBEX_ROOT/rtl \\
  -I$IBEX_ROOT/shared/rtl \\
  -I$IBEX_ROOT/vendor/lowrisc_ip/ip/prim/rtl \\
  -I$IBEX_ROOT/vendor/lowrisc_ip/dv/sv/dv_utils \\
  $IBEX_ROOT/rtl/ibex_pkg.sv \\
  $IBEX_ROOT/rtl/ibex_alu.sv \\
  $IBEX_ROOT/rtl/ibex_branch_predict.sv \\
  $IBEX_ROOT/rtl/ibex_compressed_decoder.sv \\
  $IBEX_ROOT/rtl/ibex_controller.sv \\
  $IBEX_ROOT/rtl/ibex_counter.sv \\
  $IBEX_ROOT/rtl/ibex_cs_registers.sv \\
  $IBEX_ROOT/rtl/ibex_csr.sv \\
  $IBEX_ROOT/rtl/ibex_decoder.sv \\
  $IBEX_ROOT/rtl/ibex_dummy_instr.sv \\
  $IBEX_ROOT/rtl/ibex_ex_block.sv \\
  $IBEX_ROOT/rtl/ibex_fetch_fifo.sv \\
  ./$ID_STAGE_SV \\
  $IBEX_ROOT/rtl/ibex_if_stage.sv \\
  $IBEX_ROOT/rtl/ibex_load_store_unit.sv \\
  $IBEX_ROOT/rtl/ibex_multdiv_fast.sv \\
  $IBEX_ROOT/rtl/ibex_multdiv_slow.sv \\
  $IBEX_ROOT/rtl/ibex_pmp.sv \\
  $IBEX_ROOT/rtl/ibex_prefetch_buffer.sv \\
  $IBEX_ROOT/rtl/ibex_register_file_ff.sv \\
  $IBEX_ROOT/rtl/ibex_wb_stage.sv \\
  $IBEX_ROOT/vendor/lowrisc_ip/ip/prim/rtl/prim_assert.sv \\
  ./$CORE_SV

EOFSYNTH

if [ "$WRITEBACK_STAGE" = true ]; then
    cat >> "$SYNTH_SCRIPT" << 'EOFSYNTH'
chparam -set WritebackStage 1 ibex_core

EOFSYNTH
fi

cat >> "$SYNTH_SCRIPT" << EOFSYNTH
hierarchy -check -top ibex_core
flatten
proc
opt
memory
techmap
opt

# Prepare for AIGER export - convert all DFF types to simple form
async2sync
simplemap
dfflegalize -cell \$_DFF_P_ 01 -mince 99999
clean

# Convert to AIGER format
setundef -zero
aigmap
clean
write_aiger -zinit ${BASE}_pre_abc.aig

EOFSYNTH

echo "Generated synthesis script: $SYNTH_SCRIPT"

# Step 5: Run synthesis (same as original)
echo "Running synthesis with Synlig (this may take several minutes)..."
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
echo "  - $ASSUMPTIONS_CODE (ISA + timing assumptions)"
echo "  - $CORE_SV (modified ibex_id_stage.sv with assumptions)"
echo "  - $SYNTH_SCRIPT (synthesis script)"
echo "  - ${BASE}_pre_abc.aig (AIGER for external ABC)"
echo "  - $YOSYS_LOG (Yosys synthesis log)"
echo ""

# Step 6: Run external ABC if available (EXACTLY same as original)
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

        # Two-stage optimization for best results (same as original):
        # 1. First optimize WITH constraints for maximum reduction
        # 2. Then extract clean outputs without constraints

        # Get the number of real outputs (before constraints)
        ABC_STATS=$(abc -c "read_aiger $ABC_INPUT; print_stats" 2>&1 | grep "i/o")
        if echo "$ABC_STATS" | grep -q "(c="; then
            TOTAL_OUTPUTS=$(echo "$ABC_STATS" | sed -n 's/.*i\/o = *[0-9]*\/ *\([0-9]*\).*/\1/p')
            NUM_CONSTRAINTS=$(echo "$ABC_STATS" | sed -n 's/.*c=\([0-9]*\).*/\1/p')
            REAL_OUTPUTS=$((TOTAL_OUTPUTS - NUM_CONSTRAINTS))
            echo "Detected $NUM_CONSTRAINTS constraints, will extract $REAL_OUTPUTS real outputs"
        else
            REAL_OUTPUTS=""
            echo "No constraints detected"
        fi

        if [ -n "$REAL_OUTPUTS" ]; then
            # Optimize with constraints using scorr
            abc -c "read_aiger $ABC_INPUT; strash; cycle 100; scorr -c -m -F $ABC_DEPTH -C 30000 -S 15 -v; constr -r; removepo -N 431; rewrite -l; balance -l; print_stats; write_aiger $ABC_OUTPUT" 2>&1 | tee "$ABC_LOG" | grep -E "^output|i/o =|lat =|and =|constraint|Removed equivs"
        else
            # No constraints, use standard flow
            abc -c "read_aiger $ABC_INPUT; strash; cycle 100; scorr -F $ABC_DEPTH -v; rewrite -l; balance -l; print_stats; write_aiger $ABC_OUTPUT" 2>&1 | tee "$ABC_LOG" | grep -E "^output|i/o =|lat =|and =|Removed equivs"
        fi

        # # Get the number of real outputs (before constraints)
        # ABC_STATS=$(abc -c "read_aiger $ABC_INPUT; print_stats" 2>&1 | grep "i/o")
        # if echo "$ABC_STATS" | grep -q "(c="; then
        #     TOTAL_OUTPUTS=$(echo "$ABC_STATS" | sed -n 's/.*i\/o = *[0-9]*\/ *\([0-9]*\).*/\1/p')
        #     NUM_CONSTRAINTS=$(echo "$ABC_STATS" | sed -n 's/.*c=\([0-9]*\).*/\1/p')
        #     REAL_OUTPUTS=$((TOTAL_OUTPUTS - NUM_CONSTRAINTS))
        #     echo "Detected $NUM_CONSTRAINTS constraints, will extract $REAL_OUTPUTS real outputs"
        #     # Build constraint removal commands
        #     CONSTRAINT_CMDS="constr -r; removepo -N $REAL_OUTPUTS;"
        # else
        #     REAL_OUTPUTS=""
        #     NUM_CONSTRAINTS=0
        #     echo "No constraints detected"
        #     # No constraint removal needed
        #     CONSTRAINT_CMDS=""
        # fi

        # # Pre-optimize without constraints
        # abc -c "read_aiger $ABC_INPUT; strash; dc2 -l -b; dretime; write_aiger ${BASE}_preopt.aig" 2>&1 | tee -a "$ABC_LOG"
        # # Single unified optimization flow
        # # Always use -c -m flags (they work fine even without constraints)
        # abc -c "read_aiger ${BASE}_preopt.aig; strash; cycle 100; scorr -c -m -F $ABC_DEPTH -C 30000 -S 15 -v; $CONSTRAINT_CMDS rewrite -l; balance -l; print_stats; write_aiger $ABC_OUTPUT" 2>&1 | tee "$ABC_LOG" | grep -E "^output|i/o =|lat =|and =|constraint|Removed equivs"


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

# Step 7 (optional): Gate-level synthesis (EXACTLY same as original)
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
echo "The design has been synthesized with ISA + timing constraints."
echo "Logic for outlawed instructions and impossible timing scenarios"
echo "should be optimized away via assumptions and ABC optimization."
echo ""
echo "To compare with ISA-only version:"
echo "  ./synth_ibex_with_constraints.sh $INPUT_DSL output/isa_only"
echo "  Compare the _post_abc.aig files for gate count differences"