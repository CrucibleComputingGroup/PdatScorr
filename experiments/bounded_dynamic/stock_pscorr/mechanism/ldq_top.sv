// Core = ldq with its writeback port always accepted. The environment drives the
// dispatch and memory ports. Interface assumptions are selected by defines, in the
// form a CRISP timing declaration would generate:
//   (none)        no interface assumptions (ISA-only analogue)
//   STALL_BOUND   the stock template: bound on request-acceptance stall cycles
//   TAG_LATENCY   per-tag response latency bound: a response for every accepted
//                 request arrives within LAT cycles, and only for outstanding tags
module ldq_top #(
  parameter int N   = 8,
  parameter int W   = 16,
  parameter int TW  = 3,
  parameter int LAT = 2
) (
  input  logic          clk_i,
  input  logic          rst_ni,
  input  logic          in_valid_i,
  input  logic [W-1:0]  in_addr_i,
  output logic          in_ready_o,
  output logic          req_valid_o,
  output logic [W-1:0]  req_addr_o,
  output logic [TW-1:0] req_tag_o,
  input  logic          req_ready_i,
  input  logic          rsp_valid_i,
  input  logic [TW-1:0] rsp_tag_i,
  input  logic [W-1:0]  rsp_data_i,
  output logic          wb_valid_o,
  output logic [W-1:0]  wb_data_o
);
`ifdef FORMAL_PROBE
  logic [N-1:0] busy;
`endif
  ldq #(.N(N), .W(W), .TW(TW)) core (
    .clk_i, .rst_ni, .in_valid_i, .in_addr_i, .in_ready_o, .req_valid_o, .req_addr_o,
    .req_tag_o, .req_ready_i, .rsp_valid_i, .rsp_tag_i, .rsp_data_i, .wb_valid_o,
    .wb_data_o, .wb_ready_i(1'b1)
`ifdef FORMAL_PROBE
    , .busy_o(busy)
`endif
    );
`ifdef FORMAL_PROBE
  // Ground truth only: which entries can ever be occupied under the assumptions.
  always_comb if (rst_ni) for (int i = 0; i < N; i++) cover (busy[i]);
  always_comb if ($initstate) assume (!rst_ni);  // the AIG's zero initial state is the reset state
`endif

`ifdef STALL_BOUND
  logic [2:0] stall_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) stall_q <= '0;
    else if (req_valid_o && !req_ready_i) stall_q <= stall_q + 3'd1;
    else stall_q <= '0;
  end
  always_comb begin
    if (rst_ni) begin
      assume (stall_q <= 3'(LAT));
      if (stall_q == 3'(LAT)) assume (req_ready_i);
    end
  end
`endif

`ifdef TAG_LATENCY
  logic [N-1:0] out_q;
  logic [3:0]   age_q [N];
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      out_q <= '0;
      for (int t = 0; t < N; t++) age_q[t] <= '0;
    end else begin
      for (int t = 0; t < N; t++) begin
        if (req_valid_o && req_ready_i && req_tag_o == TW'(t)) begin
          out_q[t] <= 1'b1; age_q[t] <= 4'd1;
        end else if (rsp_valid_i && rsp_tag_i == TW'(t)) begin
          out_q[t] <= 1'b0; age_q[t] <= '0;
        end else if (out_q[t]) begin
          age_q[t] <= age_q[t] + 4'd1;
        end
      end
    end
  end
  always_comb begin
    if (rst_ni) begin
      assume (req_ready_i);
      if (rsp_valid_i) assume (out_q[rsp_tag_i]);
      for (int t = 0; t < N; t++)
        if (out_q[t] && age_q[t] >= 4'(LAT)) assume (rsp_valid_i && rsp_tag_i == TW'(t));
    end
  end
`endif
endmodule
