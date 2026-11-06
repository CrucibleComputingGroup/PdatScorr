// Mechanism test: a first-free allocated table of outstanding loads, the shape of
// an MSHR or a load buffer in an in-order core with a non-blocking data port.
// Entries are allocated lowest-index first; requests carry the entry index as tag;
// responses may return out of order. Capacity N is a parameter and is never changed.
module ldq #(
  parameter int N  = 8,
  parameter int W  = 16,
  parameter int TW = 3
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
  output logic [W-1:0]  wb_data_o,
  input  logic          wb_ready_i
`ifdef FORMAL_PROBE
  , output logic [N-1:0] busy_o
`endif
);
  localparam logic [1:0] FREE = 2'd0, WAIT_REQ = 2'd1, WAIT_RSP = 2'd2, DONE = 2'd3;
  logic [1:0]   st_q   [N];
  logic [W-1:0] addr_q [N];
  logic [W-1:0] data_q [N];

  logic [TW-1:0] alloc_idx, req_idx, wb_idx;
  logic          alloc_ok, req_any, wb_any;

  always_comb begin
    alloc_ok = 1'b0; alloc_idx = '0;
    req_any  = 1'b0; req_idx   = '0;
    wb_any   = 1'b0; wb_idx    = '0;
    for (int i = N - 1; i >= 0; i--) begin
      if (st_q[i] == FREE)     begin alloc_ok = 1'b1; alloc_idx = TW'(i); end
      if (st_q[i] == WAIT_REQ) begin req_any  = 1'b1; req_idx   = TW'(i); end
      if (st_q[i] == DONE)     begin wb_any   = 1'b1; wb_idx    = TW'(i); end
    end
  end

  assign in_ready_o  = alloc_ok;
  assign req_valid_o = req_any;
  assign req_addr_o  = addr_q[req_idx];
  assign req_tag_o   = req_idx;
  assign wb_valid_o  = wb_any;
  assign wb_data_o   = data_q[wb_idx];
`ifdef FORMAL_PROBE
  for (genvar i = 0; i < N; i++) assign busy_o[i] = st_q[i] != FREE;
`endif

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      for (int i = 0; i < N; i++) begin
        st_q[i] <= FREE; addr_q[i] <= '0; data_q[i] <= '0;
      end
    end else begin
      for (int i = 0; i < N; i++) begin
        if (in_valid_i && alloc_ok && alloc_idx == TW'(i)) begin
          st_q[i] <= WAIT_REQ; addr_q[i] <= in_addr_i;
        end else if (req_any && req_ready_i && req_idx == TW'(i)) begin
          st_q[i] <= WAIT_RSP;
        end else if (rsp_valid_i && rsp_tag_i == TW'(i) && st_q[i] == WAIT_RSP) begin
          st_q[i] <= DONE; data_q[i] <= rsp_data_i;
        end else if (wb_any && wb_ready_i && wb_idx == TW'(i)) begin
          st_q[i] <= FREE;
        end
      end
    end
  end
endmodule
