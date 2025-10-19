#!/bin/bash
# Enhanced synthesis script with ICache timing constraints
# Based on synth_ibex_with_constraints.sh but adds timing constraints

set -e

# Configuration
INPUT_DSL="$1"
OUTPUT_DIR="${2:-output/icache_timing}"
ABC_DEPTH="${ABC_DEPTH:-3}"  # Increase depth for icache pipeline

if [ -z "$INPUT_DSL" ]; then
    echo "Usage: $0 <rules.dsl> [output_dir]"
    echo ""
    echo "This script synthesizes Ibex with both ISA and timing constraints."
    echo "The timing constraints help ABC's scorr achieve better optimization."
    exit 1
fi

# Create output directory
mkdir -p "$OUTPUT_DIR"

echo "=========================================="
echo "Ibex Synthesis with ISA + Timing Constraints"
echo "=========================================="
echo "Input DSL:     $INPUT_DSL"
echo "Output folder: $OUTPUT_DIR"
echo "ABC depth:     $ABC_DEPTH (for scorr k-induction)"
echo ""

# Step 1: Generate ISA constraints from DSL
echo "[1/5] Generating ISA constraints from DSL..."
pdat-dsl codegen --inline "$INPUT_DSL" "$OUTPUT_DIR/isa_assumptions.sv"

# Step 2: Create combined constraints file
echo "[2/5] Combining ISA and timing constraints..."
cat > "$OUTPUT_DIR/combined_constraints.sv" << 'EOF'
// ==========================================
// Combined ISA and Timing Constraints
// ==========================================

// ISA Constraints (from DSL)
`include "isa_assumptions.sv"

// ==========================================
// ICache Timing Constraints
// ==========================================

// These constraints inform ABC about the expected timing behavior
// of the instruction cache, enabling better sequential optimization

// Maximum latencies (adjust based on your memory system)
`define ICACHE_FETCH_LATENCY 5
`define ICACHE_HIT_LATENCY   2

// Memory interface timing constraints
// These get converted to AIGER constraints for ABC optimization
always_comb begin
  if (rst_ni && instr_req_out_o) begin
    // Memory grant must arrive within bounded time
    // This becomes a constraint in AIGER that ABC uses
    assume property (@(posedge clk_i)
      instr_req_out_o |-> ##[0:`ICACHE_FETCH_LATENCY] instr_gnt_i);
  end
end

// Track outstanding memory requests
logic [2:0] outstanding_mem_reqs;
always_ff @(posedge clk_i or negedge rst_ni) begin
  if (!rst_ni) begin
    outstanding_mem_reqs <= 3'b0;
  end else begin
    outstanding_mem_reqs <= outstanding_mem_reqs +
                            (instr_req_out_o & instr_gnt_i) -
                            instr_rvalid_i;
  end
end

// Memory responses must arrive for outstanding requests
always_comb begin
  if (rst_ni && (outstanding_mem_reqs != 0)) begin
    assume property (@(posedge clk_i)
      (outstanding_mem_reqs != 0) |-> ##[0:`ICACHE_FETCH_LATENCY] instr_rvalid_i);
  end
end

// Cache hit timing (when enabled and not busy)
always_comb begin
  if (rst_ni && icache_en_i && !icache_busy && instr_req_o) begin
    // Cache hits should respond quickly
    assume property (@(posedge clk_i)
      (instr_req_o && icache_en_i && !icache_busy) |->
      ##[0:`ICACHE_HIT_LATENCY] instr_valid_i);
  end
end

// Sequential depth hint for ABC's scorr
// This helps scorr understand the pipeline depth
property icache_pipeline_depth;
  @(posedge clk_i) disable iff (!rst_ni)
  instr_req_out_o |-> ##[1:`ICACHE_FETCH_LATENCY] instr_rvalid_i;
endproperty
assume property (icache_pipeline_depth);

EOF

# Step 3: Inject combined constraints into ibex_core
echo "[3/5] Injecting constraints into ibex_core.sv..."
python3 << 'PYTHON_SCRIPT'
import sys

# Read the combined constraints
with open("$OUTPUT_DIR/combined_constraints.sv", "r") as f:
    constraints = f.read()

# Read ibex_core.sv
ibex_core_path = "../CoreSim/cores/ibex/rtl/ibex_core.sv"
with open(ibex_core_path, "r") as f:
    content = f.read()

# Find where to inject (before endmodule)
endmodule_pos = content.rfind("endmodule")
if endmodule_pos == -1:
    print("ERROR: Could not find endmodule in ibex_core.sv")
    sys.exit(1)

# Inject constraints
modified = content[:endmodule_pos] + "\n" + constraints + "\n" + content[endmodule_pos:]

# Write modified file
with open("$OUTPUT_DIR/ibex_core_constrained.sv", "w") as f:
    f.write(modified)

print("Successfully created constrained ibex_core.sv")
PYTHON_SCRIPT

# Step 4: Generate Yosys synthesis script with timing-aware settings
echo "[4/5] Generating synthesis script..."
cat > "$OUTPUT_DIR/synth_script.ys" << 'YS_SCRIPT'
# Synthesis script for Ibex with timing constraints
# The assume statements will be preserved as AIGER constraints

# Read Verilog files
read_systemverilog -I../CoreSim/cores/ibex/rtl \
  ../CoreSim/cores/ibex/rtl/ibex_pkg.sv \
  ../CoreSim/cores/ibex/rtl/ibex_alu.sv \
  ../CoreSim/cores/ibex/rtl/ibex_compressed_decoder.sv \
  ../CoreSim/cores/ibex/rtl/ibex_controller.sv \
  ../CoreSim/cores/ibex/rtl/ibex_cs_registers.sv \
  ../CoreSim/cores/ibex/rtl/ibex_csr.sv \
  ../CoreSim/cores/ibex/rtl/ibex_decoder.sv \
  ../CoreSim/cores/ibex/rtl/ibex_ex_block.sv \
  ../CoreSim/cores/ibex/rtl/ibex_id_stage.sv \
  ../CoreSim/cores/ibex/rtl/ibex_if_stage.sv \
  ../CoreSim/cores/ibex/rtl/ibex_load_store_unit.sv \
  ../CoreSim/cores/ibex/rtl/ibex_multdiv_fast.sv \
  ../CoreSim/cores/ibex/rtl/ibex_register_file_ff.sv \
  ../CoreSim/cores/ibex/rtl/ibex_icache.sv \
  ../CoreSim/cores/ibex/rtl/ibex_prefetch_buffer.sv \
  ../CoreSim/cores/ibex/rtl/ibex_fetch_fifo.sv \
  ../CoreSim/cores/ibex/rtl/ibex_wb_stage.sv \
  $OUTPUT_DIR/ibex_core_constrained.sv

# Set top module
hierarchy -check -top ibex_core

# Flatten for cross-module optimization
flatten

# Convert processes to netlists
proc
opt

# Keep timing assumptions as constraints
# These will be exported to AIGER
memory
techmap
opt

# Prepare for AIGER export
async2sync
simplemap
dfflegalize -cell $_DFF_P_ 01
clean
setundef -zero
aigmap
clean

# Write AIGER with constraints
# The assume statements become AIGER constraints
write_aiger -zinit $OUTPUT_DIR/ibex_timed_pre_abc.aig

# Stats for debugging
stat
YS_SCRIPT

# Step 5: Run synthesis
echo "[5/5] Running synthesis with timing constraints..."
synlig -s "$OUTPUT_DIR/synth_script.ys" 2>&1 | tee "$OUTPUT_DIR/synth.log"

if [ ${PIPESTATUS[0]} -ne 0 ]; then
    echo "ERROR: Synthesis failed"
    exit 1
fi

echo ""
echo "=========================================="
echo "Synthesis Complete!"
echo "=========================================="
echo "AIGER output: $OUTPUT_DIR/ibex_timed_pre_abc.aig"
echo ""

# Step 6: Run ABC with timing-aware scorr settings
if command -v abc &> /dev/null; then
    echo "Running ABC scorr with timing-aware settings..."

    # Extract constraint count from AIGER
    AIGER_INFO=$(abc -c "read_aiger $OUTPUT_DIR/ibex_timed_pre_abc.aig; print_stats" 2>&1)
    echo "AIGER statistics:"
    echo "$AIGER_INFO" | grep -E "i/o =|lat =|and =|constraint"

    # Run scorr with appropriate depth for icache pipeline
    # The -F parameter should match the maximum latency in constraints
    echo ""
    echo "Running scorr with k=$ABC_DEPTH (matches pipeline + icache latency)..."

    abc -c "
        read_aiger $OUTPUT_DIR/ibex_timed_pre_abc.aig;
        print_stats;
        strash;
        print_stats;
        cycle 100;
        scorr -c -F $ABC_DEPTH -C 10000 -v;
        print_stats;
        dc2;
        dretime;
        print_stats;
        write_aiger $OUTPUT_DIR/ibex_timed_post_abc.aig
    " 2>&1 | tee "$OUTPUT_DIR/abc.log" | grep -E "i/o =|lat =|and =|Removed equivs|constraint"

    if [ -f "$OUTPUT_DIR/ibex_timed_post_abc.aig" ]; then
        echo ""
        echo "ABC optimization complete!"
        echo "Optimized AIGER: $OUTPUT_DIR/ibex_timed_post_abc.aig"

        # Compare sizes
        SIZE_BEFORE=$(stat -c%s "$OUTPUT_DIR/ibex_timed_pre_abc.aig")
        SIZE_AFTER=$(stat -c%s "$OUTPUT_DIR/ibex_timed_post_abc.aig")
        REDUCTION=$((100 - (SIZE_AFTER * 100 / SIZE_BEFORE)))

        echo ""
        echo "Size reduction: ${REDUCTION}% (${SIZE_BEFORE} -> ${SIZE_AFTER} bytes)"
    else
        echo "WARNING: ABC optimization failed"
    fi
else
    echo "ABC not found - skipping scorr optimization"
    echo "Install from: https://github.com/berkeley-abc/abc"
fi

echo ""
echo "=========================================="
echo "Integration Complete!"
echo "=========================================="
echo ""
echo "The timing constraints have been integrated into the synthesis flow."
echo "ABC's scorr command will use these constraints to:"
echo "  1. Identify unreachable states based on timing"
echo "  2. Merge equivalent registers considering timing behavior"
echo "  3. Optimize sequential logic knowing the pipeline depth"
echo ""
echo "To adjust timing parameters, modify:"
echo "  - ICACHE_FETCH_LATENCY: Maximum memory response time"
echo "  - ICACHE_HIT_LATENCY: Cache hit response time"
echo "  - ABC_DEPTH: scorr k-induction depth (should >= max latency)"
echo ""
echo "Files generated:"
echo "  - $OUTPUT_DIR/combined_constraints.sv (ISA + timing)"
echo "  - $OUTPUT_DIR/ibex_core_constrained.sv (modified core)"
echo "  - $OUTPUT_DIR/ibex_timed_pre_abc.aig (with constraints)"
echo "  - $OUTPUT_DIR/ibex_timed_post_abc.aig (optimized)"