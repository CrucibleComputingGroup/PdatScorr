
// ==========================================
// ICache Timing Constraints for Synthesis
// ==========================================
// These constraints help ABC scorr optimize sequential logic
// by providing information about timing relationships

`define ICACHE_FETCH_LATENCY 5
`define ICACHE_HIT_LATENCY   2
`define ICACHE_MISS_LATENCY  10
`define ICACHE_INVAL_LATENCY 20

  // Timing constraint: mem_grant_timing
  // instr_req_out_o -> instr_gnt_i within [0:5] cycles
  always_comb begin
    if (rst_ni && instr_req_out_o) begin
      assume property (@(posedge clk_i)
        instr_req_out_o |-> ##[0:5] instr_gnt_i);
    end
  end

  // Timing constraint: cache_hit_timing
  // (instr_req_o && icache_en_i && !icache_busy) -> instr_valid_i within [0:2] cycles
  always_comb begin
    if (rst_ni && icache_en_i) begin
      assume property (@(posedge clk_i)
        (instr_req_o && icache_en_i && !icache_busy) |-> ##[0:2] instr_valid_i);
    end
  end

  // Timing constraint: cache_miss_timing
  // (instr_req_o && (!icache_en_i || cache_miss)) -> instr_valid_i within [2:10] cycles
  always_comb begin
    if (rst_ni) begin
      assume property (@(posedge clk_i)
        (instr_req_o && (!icache_en_i || cache_miss)) |-> ##[2:10] instr_valid_i);
    end
  end

  // Timing constraint: cache_inval_timing
  // icache_inval_i -> !icache_busy within [1:20] cycles
  always_comb begin
    if (rst_ni) begin
      assume property (@(posedge clk_i)
        icache_inval_i |-> ##[1:20] !icache_busy);
    end
  end

  // ==========================================
  // Sequential Depth Hints for scorr
  // ==========================================
  // These properties help ABC understand the pipeline depth

  // Overall pipeline depth from request to response
  property icache_pipeline_depth;
    @(posedge clk_i) disable iff (!rst_ni)
    instr_req_out_o |-> ##[1:`ICACHE_FETCH_LATENCY] instr_rvalid_i;
  endproperty
  pipeline_depth_assume: assume property (icache_pipeline_depth);

  // Cache state machine maximum cycles
  property cache_state_cycles;
    @(posedge clk_i) disable iff (!rst_ni)
    icache_busy |-> ##[1:`ICACHE_INVAL_LATENCY] !icache_busy;
  endproperty
  cache_state_assume: assume property (cache_state_cycles);

  // Memory response ordering (pipelined slave)
  logic [3:0] req_counter, resp_counter;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      req_counter <= 4'b0;
      resp_counter <= 4'b0;
    end else begin
      req_counter <= req_counter + (instr_req_out_o & instr_gnt_i);
      resp_counter <= resp_counter + instr_rvalid_i;
    end
  end

  // Responses must eventually arrive for all requests
  always_comb begin
    if (rst_ni) begin
      assume property (@(posedge clk_i)
        (req_counter > resp_counter) |->
        ##[1:`ICACHE_FETCH_LATENCY] (resp_counter >= $past(req_counter)));
    end
  end
