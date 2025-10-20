#!/bin/bash
# Simplified test: Add timing constraints WITHOUT ISA constraints
# This focuses on demonstrating timing constraint impact

set -e

OUTPUT_DIR="${1:-output/simple_timing}"
mkdir -p "$OUTPUT_DIR"

echo "=========================================="
echo "Simple Timing Constraint Test"
echo "=========================================="
echo "This test adds ONLY timing constraints (no ISA)"
echo "to demonstrate their impact on optimization"
echo ""

# Step 1: Create a simplified Ibex wrapper with just timing constraints
echo "[1/4] Creating simplified wrapper with timing constraints..."
cat > "$OUTPUT_DIR/ibex_simple_timing.sv" << 'EOF'
// Simplified wrapper: Just adds timing constraints to memory interface
// No ISA constraints, no internal signal access

module ibex_simple_timing
  import ibex_pkg::*;
#(
  parameter rv32m_e RV32M = RV32MFast,
  parameter rv32b_e RV32B = RV32BNone
) (
  input  logic        clk_i,
  input  logic        rst_ni,

  // Instruction memory interface
  output logic        instr_req_o,
  input  logic        instr_gnt_i,
  input  logic        instr_rvalid_i,
  output logic [31:0] instr_addr_o,
  input  logic [31:0] instr_rdata_i,
  input  logic        instr_err_i,

  // Data memory interface
  output logic        data_req_o,
  input  logic        data_gnt_i,
  input  logic        data_rvalid_i,
  output logic        data_we_o,
  output logic [3:0]  data_be_o,
  output logic [31:0] data_addr_o,
  output logic [31:0] data_wdata_o,
  input  logic [31:0] data_rdata_i,
  input  logic        data_err_i,

  // Other core signals (simplified)
  input  logic        test_en_i,
  input  logic [31:0] hart_id_i,
  input  logic [31:0] boot_addr_i,
  input  logic        fetch_enable_i,
  output logic        alert_minor_o,
  output logic        alert_major_o
);

  // Instantiate simplified ibex_core
  ibex_core #(
    .RV32M(RV32M),
    .RV32B(RV32B)
  ) u_core (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .test_en_i(test_en_i),
    .scan_rst_ni(rst_ni),
    .ram_cfg_i('0),
    .hart_id_i(hart_id_i),
    .boot_addr_i(boot_addr_i),
    .instr_req_o(instr_req_o),
    .instr_gnt_i(instr_gnt_i),
    .instr_rvalid_i(instr_rvalid_i),
    .instr_addr_o(instr_addr_o),
    .instr_rdata_i(instr_rdata_i),
    .instr_err_i(instr_err_i),
    .data_req_o(data_req_o),
    .data_gnt_i(data_gnt_i),
    .data_rvalid_i(data_rvalid_i),
    .data_we_o(data_we_o),
    .data_be_o(data_be_o),
    .data_addr_o(data_addr_o),
    .data_wdata_o(data_wdata_o),
    .data_rdata_i(data_rdata_i),
    .data_err_i(data_err_i),
    .irq_software_i('0),
    .irq_timer_i('0),
    .irq_external_i('0),
    .irq_fast_i('0),
    .irq_nm_i('0),
    .debug_req_i('0),
    .crash_dump_o(),
    .double_fault_seen_o(),
    .fetch_enable_i(fetch_enable_i),
    .alert_minor_o(alert_minor_o),
    .alert_major_o(alert_major_o),
    .icache_inval_o(),
    .core_sleep_o(),
    .scan_mode_i('0)
  );

  // ==========================================
  // TIMING CONSTRAINTS (Key part!)
  // ==========================================

  // Track instruction request cycles
  logic [2:0] instr_req_cycles;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      instr_req_cycles <= '0;
    end else if (instr_req_o && !instr_gnt_i) begin
      instr_req_cycles <= instr_req_cycles + 1;
    end else begin
      instr_req_cycles <= '0;
    end
  end

  // Constraint: Instruction grant arrives within 4 cycles
  always_comb begin
    if (rst_ni) begin
      assume(instr_req_cycles <= 3'd4);
    end
  end

  // Track data request cycles
  logic [2:0] data_req_cycles;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      data_req_cycles <= '0;
    end else if (data_req_o && !data_gnt_i) begin
      data_req_cycles <= data_req_cycles + 1;
    end else begin
      data_req_cycles <= '0;
    end
  end

  // Constraint: Data grant arrives within 3 cycles
  always_comb begin
    if (rst_ni) begin
      assume(data_req_cycles <= 3'd3);
    end
  end

  // Track outstanding transactions
  logic [2:0] instr_outstanding;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      instr_outstanding <= '0;
    end else begin
      instr_outstanding <= instr_outstanding +
                          (instr_req_o & instr_gnt_i) -
                          instr_rvalid_i;
    end
  end

  logic [2:0] data_outstanding;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      data_outstanding <= '0;
    end else begin
      data_outstanding <= data_outstanding +
                         (data_req_o & data_gnt_i) -
                         data_rvalid_i;
    end
  end

  // Constraint: Bounded outstanding transactions
  always_comb begin
    if (rst_ni) begin
      assume(instr_outstanding <= 3'd4);
      assume(data_outstanding <= 3'd2);
    end
  end

endmodule
EOF

echo "Created wrapper with timing constraints"

# Step 2: Create synthesis script
echo "[2/4] Creating synthesis script..."

IBEX_ROOT="${IBEX_ROOT:-../CoreSim/cores/ibex}"

cat > "$OUTPUT_DIR/synth.ys" << EOF
# Read Ibex
read_systemverilog -I$IBEX_ROOT/rtl \\
  $IBEX_ROOT/rtl/ibex_pkg.sv \\
  $IBEX_ROOT/rtl/ibex_alu.sv \\
  $IBEX_ROOT/rtl/ibex_compressed_decoder.sv \\
  $IBEX_ROOT/rtl/ibex_controller.sv \\
  $IBEX_ROOT/rtl/ibex_cs_registers.sv \\
  $IBEX_ROOT/rtl/ibex_csr.sv \\
  $IBEX_ROOT/rtl/ibex_decoder.sv \\
  $IBEX_ROOT/rtl/ibex_ex_block.sv \\
  $IBEX_ROOT/rtl/ibex_id_stage.sv \\
  $IBEX_ROOT/rtl/ibex_if_stage.sv \\
  $IBEX_ROOT/rtl/ibex_load_store_unit.sv \\
  $IBEX_ROOT/rtl/ibex_multdiv_fast.sv \\
  $IBEX_ROOT/rtl/ibex_register_file_ff.sv \\
  $IBEX_ROOT/rtl/ibex_fetch_fifo.sv \\
  $IBEX_ROOT/rtl/ibex_prefetch_buffer.sv \\
  $IBEX_ROOT/rtl/ibex_icache.sv \\
  $IBEX_ROOT/rtl/ibex_wb_stage.sv \\
  $IBEX_ROOT/rtl/ibex_core.sv

# Read wrapper with constraints
read_systemverilog ibex_simple_timing.sv

# Synthesize
hierarchy -check -top ibex_simple_timing
flatten
proc
opt
memory
techmap
opt

# Convert to AIGER
async2sync
simplemap
dfflegalize -cell \$_DFF_P_ 01
clean
setundef -zero
aigmap
clean

write_aiger -zinit ibex_timing.aig
stat
EOF

# Step 3: Run synthesis
echo "[3/4] Running synthesis..."
cd "$OUTPUT_DIR"

if command -v synlig &> /dev/null; then
    echo "Using Synlig..."
    synlig -s synth.ys 2>&1 | tee synth.log | grep -E "cells|assume|$" | tail -15
elif command -v yosys &> /dev/null; then
    echo "Using Yosys (assumes may not work)..."
    yosys -s synth.ys 2>&1 | tee synth.log | grep -E "cells|assume|$" | tail -15
fi

cd - > /dev/null

# Step 4: Run ABC optimization
if [ -f "$OUTPUT_DIR/ibex_timing.aig" ] && command -v abc &> /dev/null; then
    echo ""
    echo "[4/4] Running ABC scorr..."

    cd "$OUTPUT_DIR"

    # Get statistics
    echo "AIGER statistics:"
    abc -c "read_aiger ibex_timing.aig; print_stats" 2>&1 | tee stats.txt

    # Check for constraints
    if grep -q "(c=" stats.txt; then
        echo "Constraints found in AIGER!"

        # Run without using constraints
        echo ""
        echo "Baseline (scorr without -c)..."
        abc -c "
            read_aiger ibex_timing.aig;
            strash;
            scorr -F 5;
            dc2; dretime;
            print_stats;
            write_aiger baseline.aig
        " 2>&1 | grep -E "and =|Removed"

        # Run using constraints
        echo ""
        echo "With constraints (scorr -c)..."
        abc -c "
            read_aiger ibex_timing.aig;
            strash;
            scorr -c -F 5 -C 10000;
            dc2; dretime;
            print_stats;
            write_aiger optimized.aig
        " 2>&1 | grep -E "and =|Removed"

        # Compare
        echo ""
        echo "=========================================="
        echo "Comparison:"

        ORIG=$(grep "and =" stats.txt | sed 's/.*and = *//' | sed 's/[^0-9].*//')
        BASE=$(abc -c "read_aiger baseline.aig; ps" 2>&1 | grep "and =" | sed 's/.*and = *//' | sed 's/[^0-9].*//')
        OPT=$(abc -c "read_aiger optimized.aig; ps" 2>&1 | grep "and =" | sed 's/.*and = *//' | sed 's/[^0-9].*//')

        echo "Original:    $ORIG AND gates"
        echo "No -c flag:  $BASE AND gates"
        echo "With -c:     $OPT AND gates"

        if [ -n "$BASE" ] && [ -n "$OPT" ] && [ "$BASE" -gt 0 ]; then
            if [ "$OPT" -lt "$BASE" ]; then
                BENEFIT=$((($BASE - $OPT) * 100 / $BASE))
                echo ""
                echo "Timing constraints provided ${BENEFIT}% additional reduction!"
            elif [ "$OPT" -gt "$BASE" ]; then
                echo ""
                echo "Warning: Constraints made it worse (may be over-constrained)"
            else
                echo ""
                echo "No difference (constraints didn't help)"
            fi
        fi
    else
        echo "No constraints found in AIGER (synthesis may have failed to preserve them)"
    fi

    cd - > /dev/null
fi

echo ""
echo "=========================================="
echo "Test Complete!"
echo "=========================================="
echo "Output: $OUTPUT_DIR"
ls -lh "$OUTPUT_DIR"/*.aig 2>/dev/null || true