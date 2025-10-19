// ==========================================
// ICache Timing Constraints for Synthesis
// ==========================================
//
// This file demonstrates how to add timing constraints for the icache
// that will be used by ABC's scorr command during circuit optimization.
//
// These constraints are similar to the ones used in formal verification
// but adapted for synthesis optimization.

module icache_timing_constraints (
  input logic clk_i,
  input logic rst_ni,

  // ICache interface signals (from ibex_core)
  input logic         instr_req_o,      // Request to memory
  input logic         instr_gnt_i,      // Grant from memory
  input logic         instr_rvalid_i,   // Response valid from memory
  input logic         instr_err_i,      // Error from memory

  // ICache internal signals (if accessible)
  input logic         icache_enable_i,
  input logic         busy_o,

  // Core interface
  input logic         req_i,            // Core requests instruction
  input logic         valid_o,          // ICache has valid instruction
  input logic         ready_i           // Core ready to accept
);

  // ========================================
  // Timing Constraint Parameters
  // ========================================

  // Maximum latency for instruction fetch (in cycles)
  // This should match your expected memory system latency
  `define ICACHE_FETCH_LATENCY 5

  // Maximum time for cache hit response (in cycles)
  `define ICACHE_HIT_LATENCY 2

  // Maximum time for cache invalidation (in cycles)
  `define ICACHE_INVAL_LATENCY 10

  // ========================================
  // Memory Interface Timing Constraints
  // ========================================

  // Constraint 1: Memory grant must arrive within bounded time
  // This helps ABC optimize based on known memory timing
  always_comb begin
    if (rst_ni && instr_req_o) begin
      // Assume grant arrives within FETCH_LATENCY cycles
      // Note: In synthesis, we use simple assumptions rather than temporal SVA
      // ABC will use these to identify unreachable states
      assume property (@(posedge clk_i)
        instr_req_o |-> ##[0:`ICACHE_FETCH_LATENCY] instr_gnt_i);
    end
  end

  // Constraint 2: Memory response valid arrives after grant
  // Track outstanding requests
  logic [3:0] outstanding_requests;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      outstanding_requests <= 4'b0;
    end else begin
      outstanding_requests <= outstanding_requests +
                              (instr_req_o & instr_gnt_i) -
                              instr_rvalid_i;
    end
  end

  // Response must arrive within bounded time after request granted
  always_comb begin
    if (rst_ni && (outstanding_requests != 0)) begin
      assume property (@(posedge clk_i)
        (outstanding_requests != 0) |-> ##[0:`ICACHE_FETCH_LATENCY] instr_rvalid_i);
    end
  end

  // ========================================
  // Cache Hit/Miss Timing Constraints
  // ========================================

  // Constraint 3: When cache is enabled and not busy,
  // valid response should come quickly (cache hit scenario)
  always_comb begin
    if (rst_ni && icache_enable_i && !busy_o && req_i) begin
      // For cache hits, response should be fast
      assume property (@(posedge clk_i)
        (req_i && icache_enable_i && !busy_o) |->
        ##[0:`ICACHE_HIT_LATENCY] valid_o);
    end
  end

  // ========================================
  // Request-Response Relationship
  // ========================================

  // Constraint 4: Valid output requires prior request
  // This helps eliminate impossible states
  always_comb begin
    if (rst_ni) begin
      // Can't have valid output without a request
      assume property (@(posedge clk_i)
        valid_o |-> $past(req_i, 1));
    end
  end

  // Constraint 5: Once valid, must stay valid until accepted
  // Standard handshake protocol
  always_comb begin
    if (rst_ni) begin
      assume property (@(posedge clk_i)
        (valid_o && !ready_i) |=> valid_o);
    end
  end

  // ========================================
  // Mutual Exclusion Constraints
  // ========================================

  // Constraint 6: Can't have both error and valid data
  always_comb begin
    if (rst_ni && valid_o) begin
      // If we have valid data, no error on memory interface
      assume (!instr_err_i || !instr_rvalid_i);
    end
  end

  // ========================================
  // Sequential Depth Hints for scorr
  // ========================================

  // These properties help scorr understand the sequential depth
  // of the icache pipeline, enabling better optimization

  // Property 1: Pipeline depth from request to response
  // This tells scorr the maximum sequential depth to consider
  property icache_pipeline_depth;
    @(posedge clk_i) disable iff (!rst_ni)
    instr_req_o |-> ##[1:`ICACHE_FETCH_LATENCY] instr_rvalid_i;
  endproperty

  // Export as assumption for synthesis
  icache_pipeline_assume: assume property (icache_pipeline_depth);

  // Property 2: Cache state machine cycles
  // Helps scorr understand state transitions
  property cache_state_transitions;
    @(posedge clk_i) disable iff (!rst_ni)
    (busy_o) |-> ##[1:`ICACHE_INVAL_LATENCY] (!busy_o);
  endproperty

  cache_state_assume: assume property (cache_state_transitions);

endmodule

// ==========================================
// Integration Helper Module
// ==========================================
//
// This shows how to instantiate the constraints in your design

module icache_with_timing_constraints import ibex_pkg::*; (
  // Original icache ports...
  input  logic        clk_i,
  input  logic        rst_ni,
  input  logic        req_i,
  input  logic        branch_i,
  input  logic [31:0] addr_i,
  // ... other ports ...

  // Memory interface
  output logic        instr_req_o,
  input  logic        instr_gnt_i,
  output logic [31:0] instr_addr_o,
  input  logic [31:0] instr_rdata_i,
  input  logic        instr_err_i,
  input  logic        instr_rvalid_i,

  // Core interface
  input  logic        ready_i,
  output logic        valid_o,
  output logic [31:0] rdata_o,
  output logic        err_o,

  // Cache control
  input  logic        icache_enable_i,
  input  logic        icache_inval_i,
  output logic        busy_o
);

  // Instantiate original icache
  ibex_icache #(
    .ICacheECC(1'b0),
    .BranchCache(1'b0)
  ) u_icache (
    .clk_i           (clk_i),
    .rst_ni          (rst_ni),
    .req_i           (req_i),
    .branch_i        (branch_i),
    .addr_i          (addr_i),
    .ready_i         (ready_i),
    .valid_o         (valid_o),
    .rdata_o         (rdata_o),
    .addr_o          (),
    .err_o           (err_o),
    .err_plus2_o     (),
    .instr_req_o     (instr_req_o),
    .instr_gnt_i     (instr_gnt_i),
    .instr_addr_o    (instr_addr_o),
    .instr_rdata_i   (instr_rdata_i),
    .instr_err_i     (instr_err_i),
    .instr_rvalid_i  (instr_rvalid_i),
    .icache_enable_i (icache_enable_i),
    .icache_inval_i  (icache_inval_i),
    .busy_o          (busy_o),
    // RAM interface (simplified)
    .ic_tag_req_o    (),
    .ic_tag_write_o  (),
    .ic_tag_addr_o   (),
    .ic_tag_wdata_o  (),
    .ic_tag_rdata_i  ('0),
    .ic_data_req_o   (),
    .ic_data_write_o (),
    .ic_data_addr_o  (),
    .ic_data_wdata_o (),
    .ic_data_rdata_i ('0),
    .ic_scr_key_valid_i (1'b0),
    .ic_scr_key_req_o   (),
    .ecc_error_o        ()
  );

  // Add timing constraints
  icache_timing_constraints u_timing_constraints (
    .clk_i           (clk_i),
    .rst_ni          (rst_ni),
    .instr_req_o     (instr_req_o),
    .instr_gnt_i     (instr_gnt_i),
    .instr_rvalid_i  (instr_rvalid_i),
    .instr_err_i     (instr_err_i),
    .icache_enable_i (icache_enable_i),
    .busy_o          (busy_o),
    .req_i           (req_i),
    .valid_o         (valid_o),
    .ready_i         (ready_i)
  );

endmodule