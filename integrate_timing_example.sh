#!/bin/bash
# Complete example: Integrate timing constraints into Ibex synthesis flow
# This combines ISA constraints (from DSL) with timing constraints

set -e

DSL_FILE="${1:-rv32im.dsl}"
OUTPUT_DIR="${2:-output/integrated_timing}"
ABC_DEPTH="${3:-5}"  # Higher depth for icache pipeline

if [ ! -f "$DSL_FILE" ]; then
    echo "Error: DSL file '$DSL_FILE' not found"
    echo "Usage: $0 [dsl_file] [output_dir] [abc_depth]"
    exit 1
fi

mkdir -p "$OUTPUT_DIR"

echo "=========================================="
echo "Ibex Synthesis with ISA + Timing Constraints"
echo "=========================================="
echo "DSL file:      $DSL_FILE"
echo "Output dir:    $OUTPUT_DIR"
echo "ABC depth:     $ABC_DEPTH"
echo ""

# Step 1: Generate ISA constraints from DSL
echo "[Step 1] Generating ISA constraints from DSL..."
pdat-dsl codegen --inline "$DSL_FILE" "$OUTPUT_DIR/isa_constraints.sv"

if [ $? -ne 0 ]; then
    echo "ERROR: Failed to generate ISA constraints"
    exit 1
fi

# Step 2: Create timing constraints for icache
echo "[Step 2] Creating timing constraints..."
cat > "$OUTPUT_DIR/timing_constraints.sv" << 'EOF'
// ==========================================
// Timing Constraints for ICache and Memory
// ==========================================
// These help ABC scorr optimize sequential logic

// Memory interface timing parameters
`define MEM_GRANT_LATENCY 3    // Max cycles for grant after request
`define MEM_DATA_LATENCY  5    // Max cycles for data after grant
`define ICACHE_HIT_LATENCY 2   // Cache hit response time

// Track outstanding memory requests
logic [2:0] outstanding_mem_requests;
always_ff @(posedge clk_i or negedge rst_ni) begin
  if (!rst_ni) begin
    outstanding_mem_requests <= 3'b0;
  end else begin
    outstanding_mem_requests <= outstanding_mem_requests +
                                (instr_req_o & instr_gnt_i) - instr_rvalid_i;
  end
end

// Constraint 1: Memory grants arrive within bounded time
always_comb begin
  if (rst_ni && instr_req_o) begin
    assume(instr_gnt_i || ($past(instr_req_o, 1) && !$past(instr_gnt_i, 1)) ||
           ($past(instr_req_o, 2) && !$past(instr_gnt_i, 2)) ||
           ($past(instr_req_o, 3) && !$past(instr_gnt_i, 3)));
  end
end

// Constraint 2: Memory responses arrive for outstanding requests
always_comb begin
  if (rst_ni && (outstanding_mem_requests > 0)) begin
    // Assume response will come within MEM_DATA_LATENCY cycles
    // This is simplified - in practice you'd use SVA or more complex logic
    assume(outstanding_mem_requests < 3'd4); // Max outstanding
  end
end

// Constraint 3: ICache state machine progress
// If icache is busy (invalidating), it completes within bounded time
always_comb begin
  if (rst_ni && icache_inval_o) begin
    // Invalidation completes within reasonable time
    assume(!$past(icache_inval_o, 20)); // Max 20 cycles
  end
end
EOF

# Step 3: Combine constraints
echo "[Step 3] Combining ISA and timing constraints..."
cat "$OUTPUT_DIR/isa_constraints.sv" > "$OUTPUT_DIR/combined_constraints.sv"
echo "" >> "$OUTPUT_DIR/combined_constraints.sv"
cat "$OUTPUT_DIR/timing_constraints.sv" >> "$OUTPUT_DIR/combined_constraints.sv"

# Step 4: Inject into ibex_id_stage.sv
echo "[Step 4] Injecting constraints into ibex_id_stage..."
IBEX_ID_STAGE="../CoreSim/cores/ibex/rtl/ibex_id_stage.sv"
if [ ! -f "$IBEX_ID_STAGE" ]; then
    IBEX_ID_STAGE="../ibex/rtl/ibex_id_stage.sv"
fi

if [ ! -f "$IBEX_ID_STAGE" ]; then
    echo "ERROR: Cannot find ibex_id_stage.sv"
    exit 1
fi

python3 scripts/inject_checker.py \
    --assumptions-file "$OUTPUT_DIR/combined_constraints.sv" \
    "$IBEX_ID_STAGE" \
    "$OUTPUT_DIR/ibex_id_stage_constrained.sv"

# Step 5: Create synthesis script
echo "[Step 5] Creating synthesis script..."
cat > "$OUTPUT_DIR/synth.ys" << 'EOF'
# Synthesis script with timing constraints

# Read Ibex with constraints
read_systemverilog -I../CoreSim/cores/ibex/rtl \
  ../CoreSim/cores/ibex/rtl/ibex_pkg.sv \
  ../CoreSim/cores/ibex/rtl/ibex_alu.sv \
  ../CoreSim/cores/ibex/rtl/ibex_compressed_decoder.sv \
  ../CoreSim/cores/ibex/rtl/ibex_controller.sv \
  ../CoreSim/cores/ibex/rtl/ibex_cs_registers.sv \
  ../CoreSim/cores/ibex/rtl/ibex_csr.sv \
  ../CoreSim/cores/ibex/rtl/ibex_decoder.sv \
  ../CoreSim/cores/ibex/rtl/ibex_ex_block.sv \
  ibex_id_stage_constrained.sv \
  ../CoreSim/cores/ibex/rtl/ibex_if_stage.sv \
  ../CoreSim/cores/ibex/rtl/ibex_load_store_unit.sv \
  ../CoreSim/cores/ibex/rtl/ibex_multdiv_fast.sv \
  ../CoreSim/cores/ibex/rtl/ibex_register_file_ff.sv \
  ../CoreSim/cores/ibex/rtl/ibex_icache.sv \
  ../CoreSim/cores/ibex/rtl/ibex_prefetch_buffer.sv \
  ../CoreSim/cores/ibex/rtl/ibex_fetch_fifo.sv \
  ../CoreSim/cores/ibex/rtl/ibex_wb_stage.sv \
  ../CoreSim/cores/ibex/rtl/ibex_core.sv

# Synthesize
hierarchy -check -top ibex_core
flatten
proc
opt

# Preserve constraints through synthesis
memory
techmap
opt

# Convert to AIGER with constraints
async2sync
simplemap
dfflegalize -cell $_DFF_P_ 01
clean
setundef -zero
aigmap
clean

# Write AIGER (constraints become C field)
write_aiger -zinit ibex_with_timing.aig

# Statistics
stat
EOF

# Step 6: Run synthesis
echo "[Step 6] Running synthesis..."
cd "$OUTPUT_DIR"
if command -v synlig &> /dev/null; then
    synlig -s synth.ys 2>&1 | tee synth.log | grep -E "Number of|assume|constraint"
else
    echo "ERROR: Synlig not found (required for SystemVerilog)"
    exit 1
fi
cd - > /dev/null

# Step 7: Run ABC with timing-aware scorr
if [ -f "$OUTPUT_DIR/ibex_with_timing.aig" ] && command -v abc &> /dev/null; then
    echo ""
    echo "[Step 7] Running ABC scorr with timing constraints..."

    cd "$OUTPUT_DIR"

    # Check AIGER
    echo "AIGER statistics:"
    abc -c "read_aiger ibex_with_timing.aig; print_stats" 2>&1 | \
        tee aiger_stats.txt | grep -E "i/o|lat|and|constraint"

    # Run baseline (no constraints)
    echo ""
    echo "Baseline optimization (without using constraints)..."
    abc -c "
        read_aiger ibex_with_timing.aig;
        strash;
        scorr -F $ABC_DEPTH -v;
        fraig;
        dc2;
        dretime;
        print_stats;
        write_aiger ibex_baseline.aig
    " 2>&1 | tee abc_baseline.log | grep -E "i/o|lat|and|Removed"

    # Run with constraints
    echo ""
    echo "Optimizing with timing constraints (-c flag)..."
    abc -c "
        read_aiger ibex_with_timing.aig;
        strash;
        scorr -c -F $ABC_DEPTH -C 10000 -v;
        fraig;
        dc2;
        dretime;
        print_stats;
        write_aiger ibex_optimized.aig
    " 2>&1 | tee abc_optimized.log | grep -E "i/o|lat|and|Removed"

    # Compare results
    echo ""
    echo "=========================================="
    echo "Optimization Results:"
    echo "=========================================="

    GATES_ORIG=$(grep "and =" aiger_stats.txt | sed 's/.*and = *//' | sed 's/[^0-9].*//')
    GATES_BASE=$(abc -c "read_aiger ibex_baseline.aig; ps" 2>&1 | grep "and =" | sed 's/.*and = *//' | sed 's/[^0-9].*//')
    GATES_OPT=$(abc -c "read_aiger ibex_optimized.aig; ps" 2>&1 | grep "and =" | sed 's/.*and = *//' | sed 's/[^0-9].*//')

    echo "Original design:          $GATES_ORIG gates"
    echo "Baseline (no -c):         $GATES_BASE gates"
    echo "With timing constraints:  $GATES_OPT gates"

    if [ -n "$GATES_ORIG" ] && [ -n "$GATES_OPT" ]; then
        REDUCTION=$((100 - (GATES_OPT * 100 / GATES_ORIG)))
        echo ""
        echo "Total reduction: ${REDUCTION}%"

        if [ -n "$GATES_BASE" ]; then
            EXTRA=$((100 - (GATES_OPT * 100 / GATES_BASE)))
            echo "Extra reduction from timing: ${EXTRA}%"
        fi
    fi

    cd - > /dev/null
else
    if [ ! -f "$OUTPUT_DIR/ibex_with_timing.aig" ]; then
        echo "ERROR: AIGER file not created"
    fi
    if ! command -v abc &> /dev/null; then
        echo "ABC not found - cannot optimize"
    fi
fi

echo ""
echo "=========================================="
echo "Integration Complete!"
echo "=========================================="
echo ""
echo "Summary:"
echo "  1. ISA constraints from DSL restrict instruction patterns"
echo "  2. Timing constraints bound memory and cache latencies"
echo "  3. Both are preserved as AIGER constraints (C field)"
echo "  4. ABC scorr -c uses them for better optimization"
echo ""
echo "Output files in $OUTPUT_DIR:"
ls -lh "$OUTPUT_DIR"/*.aig 2>/dev/null || true
echo ""
echo "To experiment with different parameters:"
echo "  - Adjust latencies in timing_constraints.sv"
echo "  - Change ABC_DEPTH to match your pipeline depth"
echo "  - Add more constraints for other modules (LSU, etc.)"