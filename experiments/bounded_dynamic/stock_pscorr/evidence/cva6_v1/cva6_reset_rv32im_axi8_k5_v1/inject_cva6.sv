
  // ========================================
  // CRISP interface wait-time bounds (per request)
  // ========================================

  // CRISP grant_latency rd 0: a raised request is accepted within 0 cycles
  logic [0:0] crisp_rd_gwait_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) crisp_rd_gwait_q <= '0;
    else if (noc_req_o.ar_valid && !noc_resp_i.ar_ready) crisp_rd_gwait_q <= crisp_rd_gwait_q + 1'd1;
    else crisp_rd_gwait_q <= '0;
  end
  always_comb begin
    if (rst_ni && noc_req_o.ar_valid && crisp_rd_gwait_q >= 1'd0) assume (noc_resp_i.ar_ready);
  end

  // CRISP grant_latency wr 0: a raised request is accepted within 0 cycles
  logic [0:0] crisp_wr_gwait_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) crisp_wr_gwait_q <= '0;
    else if (noc_req_o.aw_valid && !noc_resp_i.aw_ready) crisp_wr_gwait_q <= crisp_wr_gwait_q + 1'd1;
    else crisp_wr_gwait_q <= '0;
  end
  always_comb begin
    if (rst_ni && noc_req_o.aw_valid && crisp_wr_gwait_q >= 1'd0) assume (noc_resp_i.aw_ready);
  end

  // CRISP grant_latency wdata 0: a raised request is accepted within 0 cycles
  logic [0:0] crisp_wdata_gwait_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) crisp_wdata_gwait_q <= '0;
    else if (noc_req_o.w_valid && !noc_resp_i.w_ready) crisp_wdata_gwait_q <= crisp_wdata_gwait_q + 1'd1;
    else crisp_wdata_gwait_q <= '0;
  end
  always_comb begin
    if (rst_ni && noc_req_o.w_valid && crisp_wdata_gwait_q >= 1'd0) assume (noc_resp_i.w_ready);
  end

  // CRISP response_latency rd 8: every accepted request (tag noc_req_o.ar.id) is
  // answered 1..8 cycles after acceptance; responses only for outstanding tags
  logic [15:0] crisp_rd_out_q;
  logic [3:0] crisp_rd_age_q [16];
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      crisp_rd_out_q <= '0;
      for (int t = 0; t < 16; t++) crisp_rd_age_q[t] <= '0;
    end else begin
      for (int t = 0; t < 16; t++) begin
        if ((noc_req_o.ar_valid && noc_resp_i.ar_ready) && noc_req_o.ar.id == 4'(t)) begin
          crisp_rd_out_q[t] <= 1'b1;
          crisp_rd_age_q[t] <= 4'd1;
        end else if ((noc_resp_i.r_valid && noc_resp_i.r.last && noc_req_o.r_ready) && noc_resp_i.r.id == 4'(t)) begin
          crisp_rd_out_q[t] <= 1'b0;
          crisp_rd_age_q[t] <= '0;
        end else if (crisp_rd_out_q[t] && crisp_rd_age_q[t] < 4'd8) begin
          crisp_rd_age_q[t] <= crisp_rd_age_q[t] + 4'd1;
        end
      end
    end
  end
  always_comb begin
    if (rst_ni) begin
      if (noc_resp_i.r_valid && noc_resp_i.r.last) assume (crisp_rd_out_q[noc_resp_i.r.id]);
      for (int t = 0; t < 16; t++)
        if (crisp_rd_out_q[t] && crisp_rd_age_q[t] >= 4'd8)
          assume (noc_resp_i.r_valid && noc_resp_i.r.last && noc_resp_i.r.id == 4'(t));
    end
  end

  // CRISP response_latency wr 8: every accepted request (tag noc_req_o.aw.id) is
  // answered 1..8 cycles after acceptance; responses only for outstanding tags
  logic [15:0] crisp_wr_out_q;
  logic [3:0] crisp_wr_age_q [16];
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      crisp_wr_out_q <= '0;
      for (int t = 0; t < 16; t++) crisp_wr_age_q[t] <= '0;
    end else begin
      for (int t = 0; t < 16; t++) begin
        if ((noc_req_o.aw_valid && noc_resp_i.aw_ready) && noc_req_o.aw.id == 4'(t)) begin
          crisp_wr_out_q[t] <= 1'b1;
          crisp_wr_age_q[t] <= 4'd1;
        end else if ((noc_resp_i.b_valid && noc_req_o.b_ready) && noc_resp_i.b.id == 4'(t)) begin
          crisp_wr_out_q[t] <= 1'b0;
          crisp_wr_age_q[t] <= '0;
        end else if (crisp_wr_out_q[t] && crisp_wr_age_q[t] < 4'd8) begin
          crisp_wr_age_q[t] <= crisp_wr_age_q[t] + 4'd1;
        end
      end
    end
  end
  always_comb begin
    if (rst_ni) begin
      if (noc_resp_i.b_valid) assume (crisp_wr_out_q[noc_resp_i.b.id]);
      for (int t = 0; t < 16; t++)
        if (crisp_wr_out_q[t] && crisp_wr_age_q[t] >= 4'd8)
          assume (noc_resp_i.b_valid && noc_resp_i.b.id == 4'(t));
    end
  end

  // Pscorr reset semantics: reset is applied in the first cycle and is free afterwards
  logic pscorr_first_cycle_q = 1'b1;
  always_ff @(posedge clk_i) pscorr_first_cycle_q <= 1'b0;
  always_comb if (pscorr_first_cycle_q) assume (!rst_ni);
