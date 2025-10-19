#!/bin/bash
# Simple test of timing constraints with ABC scorr
# This demonstrates the concept without needing DSL integration

set -e

OUTPUT_DIR="${1:-output/timing_test}"
mkdir -p "$OUTPUT_DIR"

echo "=========================================="
echo "Testing Timing Constraints with ABC scorr"
echo "=========================================="

# Step 1: Create a simple test module with timing constraints
cat > "$OUTPUT_DIR/test_module.sv" << 'EOF'
// Simple test module to demonstrate timing constraints
module test_icache (
  input logic clk_i,
  input logic rst_ni,

  // Request/Grant interface (like memory)
  output logic req_o,
  input  logic gnt_i,
  output logic [31:0] addr_o,
  input  logic [31:0] data_i,
  input  logic valid_i,

  // Core interface
  input  logic fetch_req_i,
  output logic fetch_valid_o,
  output logic [31:0] fetch_data_o
);

  // Simple state machine
  typedef enum logic [1:0] {
    IDLE,
    REQUESTING,
    WAITING,
    DONE
  } state_e;

  state_e state_q, state_d;
  logic [31:0] addr_q, addr_d;
  logic [31:0] data_q, data_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= IDLE;
      addr_q <= '0;
      data_q <= '0;
    end else begin
      state_q <= state_d;
      addr_q <= addr_d;
      data_q <= data_d;
    end
  end

  always_comb begin
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
          addr_d = {fetch_req_i, 31'h12345678}; // Simple address generation
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
  // TIMING CONSTRAINTS FOR ABC OPTIMIZATION
  // ==========================================

  // Constraint 1: Memory grant arrives within 3 cycles
  property grant_timing;
    @(posedge clk_i) disable iff (!rst_ni)
    req_o |-> ##[0:3] gnt_i;
  endproperty
  assume property (grant_timing);

  // Constraint 2: Valid data arrives within 5 cycles of grant
  property data_timing;
    @(posedge clk_i) disable iff (!rst_ni)
    (req_o && gnt_i) |-> ##[1:5] valid_i;
  endproperty
  assume property (data_timing);

  // Constraint 3: Overall latency from request to valid output
  property end_to_end_timing;
    @(posedge clk_i) disable iff (!rst_ni)
    fetch_req_i |-> ##[2:8] fetch_valid_o;
  endproperty
  assume property (end_to_end_timing);

endmodule
EOF

echo "Created test module with timing constraints"

# Step 2: Create synthesis script
cat > "$OUTPUT_DIR/synth.ys" << 'EOF'
# Read the test module
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

# Export with constraints (assumes become C field in AIGER)
write_aiger -zinit test_icache.aig

# Also write statistics
stat
EOF

echo "Created synthesis script"

# Step 3: Run synthesis
echo "Running synthesis..."
cd "$OUTPUT_DIR"
if command -v yosys &> /dev/null; then
    yosys -s synth.ys 2>&1 | tee synth.log | grep -E "Number of|constraints|assume"
else
    echo "WARNING: yosys not found, trying synlig..."
    synlig -s synth.ys 2>&1 | tee synth.log | grep -E "Number of|constraints|assume"
fi
cd - > /dev/null

# Step 4: Run ABC if available
if command -v abc &> /dev/null; then
    echo ""
    echo "=========================================="
    echo "Running ABC scorr optimization"
    echo "=========================================="

    cd "$OUTPUT_DIR"

    # First, check the AIGER file
    echo "AIGER statistics before optimization:"
    abc -c "read_aiger test_icache.aig; print_stats" 2>&1 | grep -E "i/o|lat|and|constraint"

    # Run scorr WITHOUT constraints (baseline)
    echo ""
    echo "Running scorr WITHOUT using constraints (baseline)..."
    abc -c "
        read_aiger test_icache.aig;
        strash;
        scorr -F 3;
        print_stats;
        write_aiger test_no_constraints.aig
    " 2>&1 | grep -E "i/o|lat|and|Removed"

    # Run scorr WITH constraints
    echo ""
    echo "Running scorr WITH constraints (-c flag)..."
    abc -c "
        read_aiger test_icache.aig;
        strash;
        scorr -c -F 3;
        print_stats;
        write_aiger test_with_constraints.aig
    " 2>&1 | grep -E "i/o|lat|and|Removed"

    # Compare sizes
    if [ -f test_no_constraints.aig ] && [ -f test_with_constraints.aig ]; then
        SIZE_NO_C=$(stat -c%s test_no_constraints.aig)
        SIZE_WITH_C=$(stat -c%s test_with_constraints.aig)

        echo ""
        echo "=========================================="
        echo "Results Comparison:"
        echo "=========================================="
        echo "Without constraints: $SIZE_NO_C bytes"
        echo "With constraints:    $SIZE_WITH_C bytes"

        if [ $SIZE_WITH_C -lt $SIZE_NO_C ]; then
            IMPROVEMENT=$((100 - (SIZE_WITH_C * 100 / SIZE_NO_C)))
            echo "Improvement: ${IMPROVEMENT}% smaller with constraints"
        else
            echo "No improvement (constraints may be too restrictive)"
        fi
    fi

    cd - > /dev/null
else
    echo "ABC not found - cannot demonstrate scorr optimization"
    echo "Install from: https://github.com/berkeley-abc/abc"
fi

echo ""
echo "=========================================="
echo "Test Complete!"
echo "=========================================="
echo "Output directory: $OUTPUT_DIR"
echo ""
echo "Key files:"
echo "  - test_module.sv: Module with timing constraints"
echo "  - test_icache.aig: AIGER with constraints"
echo "  - test_no_constraints.aig: Optimized without using constraints"
echo "  - test_with_constraints.aig: Optimized using constraints"
echo ""
echo "The timing constraints are embedded as 'assume' properties"
echo "and exported to AIGER format where ABC can use them for"
echo "better sequential optimization with the scorr -c command."