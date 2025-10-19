#!/bin/bash
# Fixed test of timing constraints with ABC scorr

set -e

OUTPUT_DIR="${1:-output/timing_test_fixed}"
mkdir -p "$OUTPUT_DIR"

echo "=========================================="
echo "Testing Timing Constraints with ABC scorr"
echo "=========================================="

# Step 1: Create test module with timing constraints
cat > "$OUTPUT_DIR/test_module.sv" << 'EOF'
// Simple test module demonstrating timing constraints
module test_icache (
  input wire clk_i,
  input wire rst_ni,

  // Memory interface
  output reg req_o,
  input wire gnt_i,
  output reg [31:0] addr_o,
  input wire [31:0] data_i,
  input wire valid_i,

  // Core interface
  input wire fetch_req_i,
  output reg fetch_valid_o,
  output reg [31:0] fetch_data_o
);

  // Simple state machine
  reg [1:0] state_q, state_d;
  reg [31:0] addr_q, addr_d;
  reg [31:0] data_q, data_d;

  localparam IDLE = 2'b00;
  localparam REQUESTING = 2'b01;
  localparam WAITING = 2'b10;
  localparam DONE = 2'b11;

  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= IDLE;
      addr_q <= 32'b0;
      data_q <= 32'b0;
    end else begin
      state_q <= state_d;
      addr_q <= addr_d;
      data_q <= data_d;
    end
  end

  always @* begin
    state_d = state_q;
    addr_d = addr_q;
    data_d = data_q;
    req_o = 1'b0;
    addr_o = addr_q;
    fetch_valid_o = 1'b0;
    fetch_data_o = data_q;

    case (state_q)
      IDLE: begin
        if (fetch_req_i) begin
          state_d = REQUESTING;
          addr_d = 32'h12345678;
        end
      end

      REQUESTING: begin
        req_o = 1'b1;
        addr_o = addr_q;
        if (gnt_i) begin
          state_d = WAITING;
        end
      end

      WAITING: begin
        if (valid_i) begin
          data_d = data_i;
          state_d = DONE;
        end
      end

      DONE: begin
        fetch_valid_o = 1'b1;
        fetch_data_o = data_q;
        if (!fetch_req_i) begin
          state_d = IDLE;
        end
      end
    endcase
  end

  // ==========================================
  // TIMING CONSTRAINTS (as combinational assumes)
  // ==========================================

  // For ABC to use these, we create combinational constraints
  // that mark certain states as unreachable

  // Counter to track cycles since request
  reg [2:0] req_counter;
  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      req_counter <= 3'b0;
    end else if (req_o && !gnt_i) begin
      req_counter <= req_counter + 1;
    end else begin
      req_counter <= 3'b0;
    end
  end

  // Constraint: Grant must arrive within 3 cycles
  always @* begin
    if (rst_ni) begin
      assume(req_counter < 3'd4);  // Never wait more than 3 cycles
    end
  end

  // Counter for data arrival
  reg [2:0] data_counter;
  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      data_counter <= 3'b0;
    end else if (state_q == WAITING) begin
      data_counter <= data_counter + 1;
    end else begin
      data_counter <= 3'b0;
    end
  end

  // Constraint: Data arrives within 5 cycles
  always @* begin
    if (rst_ni) begin
      assume(data_counter < 3'd6);
    end
  end

endmodule
EOF

echo "Created test module: $OUTPUT_DIR/test_module.sv"

# Step 2: Create synthesis script for Synlig
cat > "$OUTPUT_DIR/synth_synlig.ys" << 'EOF'
# Read the test module using Synlig
read_systemverilog test_module.sv

# Synthesize
hierarchy -check -top test_icache
flatten
proc
opt
memory
techmap
opt

# Prepare for AIGER
async2sync
simplemap
dfflegalize -cell $_DFF_P_ 01
clean
setundef -zero
aigmap
clean

# Export with constraints
write_aiger -zinit test_icache.aig

# Statistics
stat
EOF

# Also create a regular Yosys version
cat > "$OUTPUT_DIR/synth_yosys.ys" << 'EOF'
# Read using regular Verilog
read_verilog test_module.sv

# Synthesize
hierarchy -check -top test_icache
flatten
proc
opt
memory
techmap
opt

# Prepare for AIGER
async2sync
simplemap
dfflegalize -cell $_DFF_P_ 01
clean
setundef -zero
aigmap
clean

# Export
write_aiger -zinit test_icache.aig

# Statistics
stat
EOF

echo "Created synthesis scripts"

# Step 3: Run synthesis
cd "$OUTPUT_DIR"

echo "Running synthesis..."
if command -v synlig &> /dev/null; then
    echo "Using Synlig..."
    synlig -s synth_synlig.ys 2>&1 | tee synth.log | tail -20
elif command -v yosys &> /dev/null; then
    echo "Using Yosys (note: assumes may not be preserved)..."
    yosys -s synth_yosys.ys 2>&1 | tee synth.log | tail -20
else
    echo "ERROR: Neither Synlig nor Yosys found!"
    exit 1
fi

cd - > /dev/null

# Step 4: Run ABC optimization
if [ -f "$OUTPUT_DIR/test_icache.aig" ] && command -v abc &> /dev/null; then
    echo ""
    echo "=========================================="
    echo "Running ABC scorr Optimization"
    echo "=========================================="

    cd "$OUTPUT_DIR"

    # Check AIGER statistics
    echo "AIGER file created. Statistics:"
    abc -c "read_aiger test_icache.aig; print_stats" 2>&1 | tee abc_stats.txt

    # Run scorr with different settings
    echo ""
    echo "Running scorr with k=3 (without -c flag)..."
    abc -c "
        read_aiger test_icache.aig;
        strash;
        scorr -F 3 -v;
        print_stats;
        write_aiger test_no_c.aig
    " 2>&1 | tee abc_no_c.log | grep -E "i/o|lat|and|equi"

    echo ""
    echo "Running scorr with k=3 and -c flag (using constraints)..."
    abc -c "
        read_aiger test_icache.aig;
        strash;
        scorr -c -F 3 -v;
        print_stats;
        write_aiger test_with_c.aig
    " 2>&1 | tee abc_with_c.log | grep -E "i/o|lat|and|equi"

    # Compare results
    if [ -f test_no_c.aig ] && [ -f test_with_c.aig ]; then
        echo ""
        echo "=========================================="
        echo "Comparison of Results:"
        echo "=========================================="

        # Get gate counts
        GATES_ORIG=$(grep "and =" abc_stats.txt | sed 's/.*and = *//' | sed 's/[^0-9].*//')
        GATES_NO_C=$(abc -c "read_aiger test_no_c.aig; print_stats" 2>&1 | grep "and =" | sed 's/.*and = *//' | sed 's/[^0-9].*//')
        GATES_WITH_C=$(abc -c "read_aiger test_with_c.aig; print_stats" 2>&1 | grep "and =" | sed 's/.*and = *//' | sed 's/[^0-9].*//')

        echo "Original gates:           $GATES_ORIG"
        echo "After scorr (no -c):      $GATES_NO_C"
        echo "After scorr (with -c):    $GATES_WITH_C"

        if [ -n "$GATES_ORIG" ] && [ -n "$GATES_WITH_C" ]; then
            REDUCTION=$((100 - (GATES_WITH_C * 100 / GATES_ORIG)))
            echo ""
            echo "Gate reduction with constraints: ${REDUCTION}%"
        fi
    fi

    cd - > /dev/null
else
    if [ ! -f "$OUTPUT_DIR/test_icache.aig" ]; then
        echo "ERROR: AIGER file not created"
    fi
    if ! command -v abc &> /dev/null; then
        echo "ABC not found - cannot run optimization"
        echo "Install from: https://github.com/berkeley-abc/abc"
    fi
fi

echo ""
echo "=========================================="
echo "Test Complete!"
echo "=========================================="
echo "Output directory: $OUTPUT_DIR"
echo ""
if [ -f "$OUTPUT_DIR/test_icache.aig" ]; then
    echo "Key files created:"
    echo "  - test_module.sv: Module with timing constraints"
    echo "  - test_icache.aig: AIGER format"
    ls -la "$OUTPUT_DIR"/*.aig 2>/dev/null || true
fi