#!/bin/bash
# Synthesis with timing constraints using Option 2 (separate constraint module)
# This keeps the original Ibex RTL completely untouched

set -e

# Parse arguments
DSL_FILE="${1:-rv32im.dsl}"
OUTPUT_DIR="${2:-output/option2_timing}"
ABC_DEPTH="${ABC_DEPTH:-5}"  # Higher for timing constraints

if [ ! -f "$DSL_FILE" ]; then
    echo "Usage: $0 <rules.dsl> [output_dir]"
    echo ""
    echo "This script synthesizes Ibex with ISA + timing constraints"
    echo "using Option 2: separate constraint module (original RTL untouched)"
    exit 1
fi

# Extract DSL base name for subfolder
DSL_BASENAME=$(basename "$DSL_FILE" .dsl)
OUTPUT_DIR="$OUTPUT_DIR/$DSL_BASENAME"
mkdir -p "$OUTPUT_DIR"

echo "=========================================="
echo "Ibex Synthesis with Timing (Option 2)"
echo "=========================================="
echo "Input DSL:     $DSL_FILE"
echo "Output folder: $OUTPUT_DIR"
echo "Approach:      Separate constraint module (RTL untouched)"
echo ""

# Step 1: Generate ISA constraints from DSL
echo "[1/7] Generating ISA constraints from DSL..."
pdat-dsl codegen --inline "$DSL_FILE" "$OUTPUT_DIR/isa_constraints.sv"

if [ $? -ne 0 ]; then
    echo "ERROR: Failed to generate ISA constraints"
    exit 1
fi

# Step 2: Create timing constraint module (SEPARATE, not injected)
echo "[2/7] Creating separate timing constraint module..."
cat > "$OUTPUT_DIR/ibex_timing_constraints.sv" << 'EOF'
// ==========================================
// Timing Constraints Module for Ibex
// ==========================================
// This module observes Ibex signals and adds timing assumptions
// It does NOT modify any Ibex RTL - just observes and constrains

module ibex_timing_constraints (
  input logic clk_i,
  input logic rst_ni,

  // Observe instruction memory interface
  input logic        instr_req_o,
  input logic        instr_gnt_i,
  input logic        instr_rvalid_i,
  input logic [31:0] instr_rdata_i,
  input logic        instr_err_i,

  // Observe data memory interface
  input logic        data_req_o,
  input logic        data_gnt_i,
  input logic        data_rvalid_i,
  input logic        data_we_o,
  input logic [31:0] data_rdata_i,
  input logic        data_err_i
);

  // ==========================================
  // Timing Parameters (adjust for your memory system)
  // ==========================================
  localparam int INSTR_GRANT_MAX_CYCLES = 3;
  localparam int INSTR_RVALID_MAX_CYCLES = 5;
  localparam int DATA_GRANT_MAX_CYCLES = 4;
  localparam int DATA_RVALID_MAX_CYCLES = 6;

  // ==========================================
  // Instruction Memory Constraints
  // ==========================================

  // Track cycles waiting for grant
  logic [2:0] instr_grant_counter;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      instr_grant_counter <= 3'b0;
    end else if (!instr_req_o) begin
      instr_grant_counter <= 3'b0;
    end else if (instr_req_o && !instr_gnt_i) begin
      instr_grant_counter <= instr_grant_counter + 1;
    end else begin
      instr_grant_counter <= 3'b0;
    end
  end

  // Constraint: instruction grant must arrive within bound
  always_comb begin
    if (rst_ni) begin
      assume(instr_grant_counter <= INSTR_GRANT_MAX_CYCLES);
    end
  end

  // Track outstanding instruction requests
  logic [2:0] instr_outstanding;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      instr_outstanding <= 3'b0;
    end else begin
      instr_outstanding <= instr_outstanding +
                           (instr_req_o & instr_gnt_i) -
                           instr_rvalid_i;
    end
  end

  // Track cycles waiting for instruction response
  logic [2:0] instr_rvalid_counter;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      instr_rvalid_counter <= 3'b0;
    end else if (instr_outstanding == 0) begin
      instr_rvalid_counter <= 3'b0;
    end else if (!instr_rvalid_i) begin
      instr_rvalid_counter <= instr_rvalid_counter + 1;
    end else begin
      instr_rvalid_counter <= 3'b0;
    end
  end

  // Constraint: instruction response must arrive within bound
  always_comb begin
    if (rst_ni && (instr_outstanding > 0)) begin
      assume(instr_rvalid_counter <= INSTR_RVALID_MAX_CYCLES);
    end
  end

  // ==========================================
  // Data Memory Constraints
  // ==========================================

  // Track cycles waiting for data grant
  logic [2:0] data_grant_counter;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      data_grant_counter <= 3'b0;
    end else if (!data_req_o) begin
      data_grant_counter <= 3'b0;
    end else if (data_req_o && !data_gnt_i) begin
      data_grant_counter <= data_grant_counter + 1;
    end else begin
      data_grant_counter <= 3'b0;
    end
  end

  // Constraint: data grant must arrive within bound
  always_comb begin
    if (rst_ni) begin
      assume(data_grant_counter <= DATA_GRANT_MAX_CYCLES);
    end
  end

  // Track outstanding data requests
  logic [2:0] data_outstanding;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      data_outstanding <= 3'b0;
    end else begin
      data_outstanding <= data_outstanding +
                         (data_req_o & data_gnt_i) -
                         data_rvalid_i;
    end
  end

  // Constraint: data response must arrive within bound
  logic [2:0] data_rvalid_counter;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      data_rvalid_counter <= 3'b0;
    end else if (data_outstanding == 0) begin
      data_rvalid_counter <= 3'b0;
    end else if (!data_rvalid_i) begin
      data_rvalid_counter <= data_rvalid_counter + 1;
    end else begin
      data_rvalid_counter <= 3'b0;
    end
  end

  always_comb begin
    if (rst_ni && (data_outstanding > 0)) begin
      assume(data_rvalid_counter <= DATA_RVALID_MAX_CYCLES);
    end
  end

  // ==========================================
  // Protocol Constraints
  // ==========================================

  // Can't have both instruction and data errors at same time
  always_comb begin
    if (rst_ni) begin
      assume(!(instr_err_i && data_err_i));
    end
  end

  // Maximum outstanding transactions
  always_comb begin
    if (rst_ni) begin
      assume(instr_outstanding <= 3'd4);
      assume(data_outstanding <= 3'd2);
    end
  end

endmodule
EOF

echo "Created timing constraint module"

# Step 3: Create ISA constraint module (also separate)
echo "[3/7] Creating separate ISA constraint module..."
cat > "$OUTPUT_DIR/ibex_isa_constraints.sv" << EOF
// ==========================================
// ISA Constraints Module for Ibex
// ==========================================
// Generated from DSL, observes instruction stream

module ibex_isa_constraints (
  input logic clk_i,
  input logic rst_ni,
  input logic        instr_valid_i,
  input logic [31:0] instr_rdata_i,
  input logic        instr_is_compressed_i
);

// Include the generated ISA constraints
\`include "isa_constraints.sv"

endmodule
EOF

echo "Created ISA constraint module"

# Step 4: Create wrapper that instantiates Ibex + constraints
echo "[4/7] Creating wrapper module..."
cat > "$OUTPUT_DIR/ibex_constrained_wrapper.sv" << 'EOF'
// ==========================================
// Wrapper: Ibex Core + Constraints
// ==========================================
// This instantiates the ORIGINAL ibex_core (untouched)
// plus separate constraint modules

module ibex_constrained_wrapper
  import ibex_pkg::*;
#(
  parameter bit                 PMPEnable         = 1'b0,
  parameter int unsigned         PMPGranularity    = 0,
  parameter int unsigned         PMPNumRegions     = 4,
  parameter int unsigned         MHPMCounterNum    = 0,
  parameter int unsigned         MHPMCounterWidth  = 40,
  parameter bit                  RV32E             = 1'b0,
  parameter rv32m_e              RV32M             = RV32MFast,
  parameter rv32b_e              RV32B             = RV32BNone,
  parameter regfile_e            RegFile           = RegFileFF,
  parameter bit                  BranchTargetALU   = 1'b0,
  parameter bit                  WritebackStage    = 1'b0,
  parameter bit                  ICache            = 1'b0,
  parameter bit                  ICacheECC         = 1'b0,
  parameter int unsigned         BusSizeECC        = BUS_SIZE,
  parameter int unsigned         TagSizeECC        = IC_TAG_SIZE,
  parameter int unsigned         LineSizeECC       = IC_LINE_SIZE,
  parameter bit                  BranchPredictor   = 1'b0,
  parameter bit                  DbgTriggerEn      = 1'b0,
  parameter int unsigned         DbgHwBreakNum     = 1,
  parameter bit                  SecureIbex        = 1'b0,
  parameter int unsigned         DmHaltAddr        = 32'h1A110800,
  parameter int unsigned         DmExceptionAddr   = 32'h1A110808
) (
  // Clock and Reset
  input  logic                         clk_i,
  input  logic                         rst_ni,
  input  logic                         test_en_i,
  input  logic                         scan_rst_ni,
  input  logic [31:0]                  ram_cfg_i,
  input  logic [31:0]                  hart_id_i,
  input  logic [31:0]                  boot_addr_i,

  // Instruction memory interface
  output logic                         instr_req_o,
  input  logic                         instr_gnt_i,
  input  logic                         instr_rvalid_i,
  output logic [31:0]                  instr_addr_o,
  input  logic [31:0]                  instr_rdata_i,
  input  logic                         instr_err_i,

  // Data memory interface
  output logic                         data_req_o,
  input  logic                         data_gnt_i,
  input  logic                         data_rvalid_i,
  output logic                         data_we_o,
  output logic [3:0]                   data_be_o,
  output logic [31:0]                  data_addr_o,
  output logic [31:0]                  data_wdata_o,
  input  logic [31:0]                  data_rdata_i,
  input  logic                         data_err_i,

  // Interrupt inputs
  input  logic                         irq_software_i,
  input  logic                         irq_timer_i,
  input  logic                         irq_external_i,
  input  logic [14:0]                  irq_fast_i,
  input  logic                         irq_nm_i,

  // Debug Interface
  input  logic                         debug_req_i,
  output crash_dump_t                  crash_dump_o,

  // RISC-V Formal Interface
  output logic                         rvfi_valid,
  output logic [63:0]                  rvfi_order,
  output logic [31:0]                  rvfi_insn,
  output logic                         rvfi_trap,
  output logic                         rvfi_halt,
  output logic                         rvfi_intr,
  output logic [ 1:0]                  rvfi_mode,
  output logic [ 1:0]                  rvfi_ixl,
  output logic [ 4:0]                  rvfi_rs1_addr,
  output logic [ 4:0]                  rvfi_rs2_addr,
  output logic [ 4:0]                  rvfi_rs3_addr,
  output logic [31:0]                  rvfi_rs1_rdata,
  output logic [31:0]                  rvfi_rs2_rdata,
  output logic [31:0]                  rvfi_rs3_rdata,
  output logic [ 4:0]                  rvfi_rd_addr,
  output logic [31:0]                  rvfi_rd_wdata,
  output logic [31:0]                  rvfi_pc_rdata,
  output logic [31:0]                  rvfi_pc_wdata,
  output logic [31:0]                  rvfi_mem_addr,
  output logic [ 3:0]                  rvfi_mem_rmask,
  output logic [ 3:0]                  rvfi_mem_wmask,
  output logic [31:0]                  rvfi_mem_rdata,
  output logic [31:0]                  rvfi_mem_wdata,
  output logic [31:0]                  rvfi_ext_mip,
  output logic [31:0]                  rvfi_ext_nmi,
  output logic [31:0]                  rvfi_ext_debug_req,
  output logic [63:0]                  rvfi_ext_mcycle,

  // CPU Control Signals
  input  logic                         fetch_enable_i,
  output logic                         alert_minor_o,
  output logic                         alert_major_o,
  output logic                         core_sleep_o,

  // DFT bypass controls
  input logic                          scan_mode_i
);

  // ==========================================
  // Instantiate ORIGINAL ibex_core (untouched)
  // ==========================================

  // Internal signals for observing core state
  logic        instr_valid;
  logic [31:0] instr_rdata;
  logic        instr_is_compressed;

  ibex_core #(
    .PMPEnable        (PMPEnable),
    .PMPGranularity   (PMPGranularity),
    .PMPNumRegions    (PMPNumRegions),
    .MHPMCounterNum   (MHPMCounterNum),
    .MHPMCounterWidth (MHPMCounterWidth),
    .RV32E            (RV32E),
    .RV32M            (RV32M),
    .RV32B            (RV32B),
    .RegFile          (RegFile),
    .BranchTargetALU  (BranchTargetALU),
    .WritebackStage   (WritebackStage),
    .ICache           (ICache),
    .ICacheECC        (ICacheECC),
    .BusSizeECC       (BusSizeECC),
    .TagSizeECC       (TagSizeECC),
    .LineSizeECC      (LineSizeECC),
    .BranchPredictor  (BranchPredictor),
    .DbgTriggerEn     (DbgTriggerEn),
    .DbgHwBreakNum    (DbgHwBreakNum),
    .SecureIbex       (SecureIbex),
    .DmHaltAddr       (DmHaltAddr),
    .DmExceptionAddr  (DmExceptionAddr)
  ) u_ibex_core (
    // Connect all ports
    .clk_i            (clk_i),
    .rst_ni           (rst_ni),
    .test_en_i        (test_en_i),
    .scan_rst_ni      (scan_rst_ni),
    .ram_cfg_i        (ram_cfg_i),
    .hart_id_i        (hart_id_i),
    .boot_addr_i      (boot_addr_i),
    .instr_req_o      (instr_req_o),
    .instr_gnt_i      (instr_gnt_i),
    .instr_rvalid_i   (instr_rvalid_i),
    .instr_addr_o     (instr_addr_o),
    .instr_rdata_i    (instr_rdata_i),
    .instr_err_i      (instr_err_i),
    .data_req_o       (data_req_o),
    .data_gnt_i       (data_gnt_i),
    .data_rvalid_i    (data_rvalid_i),
    .data_we_o        (data_we_o),
    .data_be_o        (data_be_o),
    .data_addr_o      (data_addr_o),
    .data_wdata_o     (data_wdata_o),
    .data_rdata_i     (data_rdata_i),
    .data_err_i       (data_err_i),
    .irq_software_i   (irq_software_i),
    .irq_timer_i      (irq_timer_i),
    .irq_external_i   (irq_external_i),
    .irq_fast_i       (irq_fast_i),
    .irq_nm_i         (irq_nm_i),
    .debug_req_i      (debug_req_i),
    .crash_dump_o     (crash_dump_o),
    .rvfi_valid       (rvfi_valid),
    .rvfi_order       (rvfi_order),
    .rvfi_insn        (rvfi_insn),
    .rvfi_trap        (rvfi_trap),
    .rvfi_halt        (rvfi_halt),
    .rvfi_intr        (rvfi_intr),
    .rvfi_mode        (rvfi_mode),
    .rvfi_ixl         (rvfi_ixl),
    .rvfi_rs1_addr    (rvfi_rs1_addr),
    .rvfi_rs2_addr    (rvfi_rs2_addr),
    .rvfi_rs3_addr    (rvfi_rs3_addr),
    .rvfi_rs1_rdata   (rvfi_rs1_rdata),
    .rvfi_rs2_rdata   (rvfi_rs2_rdata),
    .rvfi_rs3_rdata   (rvfi_rs3_rdata),
    .rvfi_rd_addr     (rvfi_rd_addr),
    .rvfi_rd_wdata    (rvfi_rd_wdata),
    .rvfi_pc_rdata    (rvfi_pc_rdata),
    .rvfi_pc_wdata    (rvfi_pc_wdata),
    .rvfi_mem_addr    (rvfi_mem_addr),
    .rvfi_mem_rmask   (rvfi_mem_rmask),
    .rvfi_mem_wmask   (rvfi_mem_wmask),
    .rvfi_mem_rdata   (rvfi_mem_rdata),
    .rvfi_mem_wdata   (rvfi_mem_wdata),
    .rvfi_ext_mip     (rvfi_ext_mip),
    .rvfi_ext_nmi     (rvfi_ext_nmi),
    .rvfi_ext_debug_req(rvfi_ext_debug_req),
    .rvfi_ext_mcycle  (rvfi_ext_mcycle),
    .fetch_enable_i   (fetch_enable_i),
    .alert_minor_o    (alert_minor_o),
    .alert_major_o    (alert_major_o),
    .core_sleep_o     (core_sleep_o),
    .scan_mode_i      (scan_mode_i)
  );

  // ==========================================
  // Extract internal signals for constraints
  // ==========================================
  // We need to observe the instruction in ID stage
  // This is a bit of a hack but avoids modifying ibex_core
  assign instr_valid = u_ibex_core.id_stage_i.instr_valid_i;
  assign instr_rdata = u_ibex_core.id_stage_i.instr_rdata_i;
  assign instr_is_compressed = u_ibex_core.id_stage_i.instr_is_compressed_i;

  // ==========================================
  // Instantiate timing constraints (Option 2)
  // ==========================================
  ibex_timing_constraints u_timing_constraints (
    .clk_i            (clk_i),
    .rst_ni           (rst_ni),
    .instr_req_o      (instr_req_o),
    .instr_gnt_i      (instr_gnt_i),
    .instr_rvalid_i   (instr_rvalid_i),
    .instr_rdata_i    (instr_rdata_i),
    .instr_err_i      (instr_err_i),
    .data_req_o       (data_req_o),
    .data_gnt_i       (data_gnt_i),
    .data_rvalid_i    (data_rvalid_i),
    .data_we_o        (data_we_o),
    .data_rdata_i     (data_rdata_i),
    .data_err_i       (data_err_i)
  );

  // ==========================================
  // Instantiate ISA constraints (Option 2)
  // ==========================================
  ibex_isa_constraints u_isa_constraints (
    .clk_i                 (clk_i),
    .rst_ni                (rst_ni),
    .instr_valid_i         (instr_valid),
    .instr_rdata_i         (instr_rdata),
    .instr_is_compressed_i (instr_is_compressed)
  );

endmodule
EOF

echo "Created wrapper module"

# Step 5: Create synthesis script
echo "[5/7] Creating synthesis script..."

IBEX_ROOT="${IBEX_ROOT:-../CoreSim/cores/ibex}"
IBEX_ROOT=$(realpath "$IBEX_ROOT")

cat > "$OUTPUT_DIR/synth.ys" << EOF
# Synthesis script for Option 2 (wrapper with constraints)
# The original Ibex RTL is completely untouched

# Set include directories
verilog_defaults -add -I$IBEX_ROOT/rtl
verilog_defaults -add -I$IBEX_ROOT/shared/rtl
verilog_defaults -add -I$IBEX_ROOT/vendor/lowrisc_ip/ip/prim/rtl
verilog_defaults -add -I$IBEX_ROOT/vendor/lowrisc_ip/dv/sv/dv_utils

# Read all Ibex files (ORIGINAL, UNTOUCHED)
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
  $IBEX_ROOT/rtl/ibex_id_stage.sv \\
  $IBEX_ROOT/rtl/ibex_if_stage.sv \\
  $IBEX_ROOT/rtl/ibex_load_store_unit.sv \\
  $IBEX_ROOT/rtl/ibex_multdiv_fast.sv \\
  $IBEX_ROOT/rtl/ibex_multdiv_slow.sv \\
  $IBEX_ROOT/rtl/ibex_pmp.sv \\
  $IBEX_ROOT/rtl/ibex_prefetch_buffer.sv \\
  $IBEX_ROOT/rtl/ibex_register_file_ff.sv \\
  $IBEX_ROOT/rtl/ibex_wb_stage.sv \\
  $IBEX_ROOT/rtl/ibex_icache.sv \\
  $IBEX_ROOT/vendor/lowrisc_ip/ip/prim/rtl/prim_assert.sv \\
  $IBEX_ROOT/rtl/ibex_core.sv

# Read constraint modules and wrapper
read_systemverilog \\
  -I. \\
  ibex_timing_constraints.sv \\
  ibex_isa_constraints.sv \\
  ibex_constrained_wrapper.sv

# Use the wrapper as top module
hierarchy -check -top ibex_constrained_wrapper

# Flatten to enable optimization
flatten

# Synthesis
proc
opt
memory
techmap
opt

# Prepare for AIGER
async2sync
simplemap
dfflegalize -cell \$_DFF_P_ 01
clean
setundef -zero
aigmap
clean

# Write AIGER with constraints
write_aiger -zinit ibex_option2.aig

# Statistics
stat
EOF

echo "Created synthesis script"

# Step 6: Run synthesis
echo "[6/7] Running synthesis..."
cd "$OUTPUT_DIR"

if command -v synlig &> /dev/null; then
    synlig -s synth.ys 2>&1 | tee synth.log | grep -E "Number of|assume|cells" | tail -20
else
    echo "ERROR: Synlig not found (required for SystemVerilog)"
    exit 1
fi

cd - > /dev/null

# Step 7: Run ABC with and without constraints
if [ -f "$OUTPUT_DIR/ibex_option2.aig" ] && command -v abc &> /dev/null; then
    echo ""
    echo "[7/7] Running ABC scorr optimization..."

    cd "$OUTPUT_DIR"

    # Check AIGER
    echo "AIGER statistics:"
    abc -c "read_aiger ibex_option2.aig; print_stats" 2>&1 | tee aiger_stats.txt

    # Extract constraint count
    CONSTRAINT_COUNT=$(grep -o "(c=[0-9]*)" aiger_stats.txt | sed 's/[^0-9]//g')
    if [ -n "$CONSTRAINT_COUNT" ]; then
        echo "Found $CONSTRAINT_COUNT constraints in AIGER"
    fi

    # Baseline: no constraints used
    echo ""
    echo "Baseline optimization (scorr without -c)..."
    abc -c "
        read_aiger ibex_option2.aig;
        strash;
        scorr -F $ABC_DEPTH -v;
        fraig;
        dc2;
        dretime;
        print_stats;
        write_aiger ibex_baseline.aig
    " 2>&1 | tee abc_baseline.log | grep -E "i/o|lat|and|Removed"

    # With constraints
    echo ""
    echo "Optimization with timing constraints (scorr -c)..."
    abc -c "
        read_aiger ibex_option2.aig;
        strash;
        scorr -c -F $ABC_DEPTH -C 10000 -v;
        fraig;
        dc2;
        dretime;
        print_stats;
        write_aiger ibex_optimized.aig
    " 2>&1 | tee abc_optimized.log | grep -E "i/o|lat|and|Removed"

    # Compare
    echo ""
    echo "=========================================="
    echo "Results Comparison:"
    echo "=========================================="

    GATES_ORIG=$(grep "and =" aiger_stats.txt | sed 's/.*and = *//' | sed 's/[^0-9].*//')
    GATES_BASE=$(abc -c "read_aiger ibex_baseline.aig; ps" 2>&1 | grep "and =" | sed 's/.*and = *//' | sed 's/[^0-9].*//')
    GATES_OPT=$(abc -c "read_aiger ibex_optimized.aig; ps" 2>&1 | grep "and =" | sed 's/.*and = *//' | sed 's/[^0-9].*//')

    echo "Original with constraints: $GATES_ORIG gates"
    echo "After scorr (no -c):       $GATES_BASE gates"
    echo "After scorr (with -c):     $GATES_OPT gates"

    if [ -n "$GATES_ORIG" ] && [ -n "$GATES_BASE" ] && [ -n "$GATES_OPT" ]; then
        if [ "$GATES_BASE" -gt 0 ]; then
            IMPROVEMENT=$((($GATES_BASE - $GATES_OPT) * 100 / $GATES_BASE))
            echo ""
            echo "Improvement from using constraints: ${IMPROVEMENT}%"

            TOTAL_REDUCTION=$((($GATES_ORIG - $GATES_OPT) * 100 / $GATES_ORIG))
            echo "Total reduction from original: ${TOTAL_REDUCTION}%"
        fi
    fi

    cd - > /dev/null
else
    if [ ! -f "$OUTPUT_DIR/ibex_option2.aig" ]; then
        echo "ERROR: AIGER file not created"
    fi
    if ! command -v abc &> /dev/null; then
        echo "ABC not found - cannot run optimization"
    fi
fi

echo ""
echo "=========================================="
echo "Option 2 Synthesis Complete!"
echo "=========================================="
echo ""
echo "Key advantages of Option 2:"
echo "  1. Original Ibex RTL completely untouched"
echo "  2. Constraints clearly separated in their own modules"
echo "  3. Easy to adjust timing parameters without touching Ibex"
echo "  4. Can enable/disable constraint modules independently"
echo ""
echo "Output directory: $OUTPUT_DIR"
ls -lh "$OUTPUT_DIR"/*.aig 2>/dev/null || true
echo ""
echo "To adjust timing parameters, edit:"
echo "  - INSTR_GRANT_MAX_CYCLES in ibex_timing_constraints.sv"
echo "  - DATA_GRANT_MAX_CYCLES, etc."