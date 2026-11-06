
  // ========================================
  // CRISP interface wait-time bounds (per request)
  // ========================================

  // CRISP grant_latency instr 0: a raised request is accepted within 0 cycles
  logic [0:0] crisp_instr_gwait_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) crisp_instr_gwait_q <= '0;
    else if (instr_req_o && !instr_gnt_i) crisp_instr_gwait_q <= crisp_instr_gwait_q + 1'd1;
    else crisp_instr_gwait_q <= '0;
  end
  always_comb begin
    if (rst_ni && instr_req_o && crisp_instr_gwait_q >= 1'd0) assume (instr_gnt_i);
  end

  // CRISP response_latency instr 2: in-order responses; every accepted request is
  // answered 1..2 cycles after acceptance (the monitor tracks up to 4 outstanding)
  logic [2:0] crisp_instr_cnt_q, crisp_instr_cnt_d;
  logic [1:0] crisp_instr_age_q [4];
  logic [1:0] crisp_instr_age_d [4];
  wire crisp_instr_push = (instr_req_o && instr_gnt_i) && (crisp_instr_cnt_q < 3'd4 || (instr_rvalid_i && instr_rready_o));
  wire crisp_instr_pop  = (instr_rvalid_i && instr_rready_o) && crisp_instr_cnt_q != '0;
  function automatic logic [1:0] crisp_instr_inc(input logic [1:0] a);
    return (a < 2'd2) ? a + 2'd1 : a;
  endfunction
  always_comb begin
    for (int i = 0; i < 4; i++) crisp_instr_age_d[i] = '0;
    if (crisp_instr_pop) begin
      if (1 < crisp_instr_cnt_q) crisp_instr_age_d[0] = crisp_instr_inc(crisp_instr_age_q[1]);
    end else if (0 < crisp_instr_cnt_q) crisp_instr_age_d[0] = crisp_instr_inc(crisp_instr_age_q[0]);
    if (crisp_instr_pop) begin
      if (2 < crisp_instr_cnt_q) crisp_instr_age_d[1] = crisp_instr_inc(crisp_instr_age_q[2]);
    end else if (1 < crisp_instr_cnt_q) crisp_instr_age_d[1] = crisp_instr_inc(crisp_instr_age_q[1]);
    if (crisp_instr_pop) begin
      if (3 < crisp_instr_cnt_q) crisp_instr_age_d[2] = crisp_instr_inc(crisp_instr_age_q[3]);
    end else if (2 < crisp_instr_cnt_q) crisp_instr_age_d[2] = crisp_instr_inc(crisp_instr_age_q[2]);
    if (!crisp_instr_pop && 3 < crisp_instr_cnt_q) crisp_instr_age_d[3] = crisp_instr_inc(crisp_instr_age_q[3]);
    crisp_instr_cnt_d = crisp_instr_cnt_q - 3'(crisp_instr_pop);
    if (crisp_instr_push) begin
      crisp_instr_age_d[crisp_instr_cnt_d] = 2'd1;
      crisp_instr_cnt_d = crisp_instr_cnt_d + 3'd1;
    end
  end
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      crisp_instr_cnt_q <= '0;
      for (int i = 0; i < 4; i++) crisp_instr_age_q[i] <= '0;
    end else begin
      crisp_instr_cnt_q <= crisp_instr_cnt_d;
      for (int i = 0; i < 4; i++) crisp_instr_age_q[i] <= crisp_instr_age_d[i];
    end
  end
  always_comb begin
    if (rst_ni) begin
      if (instr_rvalid_i) assume (crisp_instr_cnt_q != '0);
      if (crisp_instr_cnt_q != '0 && crisp_instr_age_q[0] >= 2'd2) assume (instr_rvalid_i);
    end
  end

  // CRISP grant_latency data_load 0: a raised request is accepted within 0 cycles
  logic [0:0] crisp_data_load_gwait_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) crisp_data_load_gwait_q <= '0;
    else if (data_load_req_o && !data_load_gnt_i) crisp_data_load_gwait_q <= crisp_data_load_gwait_q + 1'd1;
    else crisp_data_load_gwait_q <= '0;
  end
  always_comb begin
    if (rst_ni && data_load_req_o && crisp_data_load_gwait_q >= 1'd0) assume (data_load_gnt_i);
  end

  // CRISP response_latency data_load 3: every accepted request (tag data_load_tag_o) is
  // answered 1..3 cycles after acceptance; responses only for outstanding tags
  logic [15:0] crisp_data_load_out_q;
  logic [2:0] crisp_data_load_age_q [16];
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      crisp_data_load_out_q <= '0;
      for (int t = 0; t < 16; t++) crisp_data_load_age_q[t] <= '0;
    end else begin
      for (int t = 0; t < 16; t++) begin
        if ((data_load_req_o && data_load_gnt_i) && data_load_tag_o == 4'(t)) begin
          crisp_data_load_out_q[t] <= 1'b1;
          crisp_data_load_age_q[t] <= 3'd1;
        end else if ((data_load_rvalid_i && data_load_rready_o) && data_load_tag_i == 4'(t)) begin
          crisp_data_load_out_q[t] <= 1'b0;
          crisp_data_load_age_q[t] <= '0;
        end else if (crisp_data_load_out_q[t] && crisp_data_load_age_q[t] < 3'd3) begin
          crisp_data_load_age_q[t] <= crisp_data_load_age_q[t] + 3'd1;
        end
      end
    end
  end
  always_comb begin
    if (rst_ni) begin
      if (data_load_rvalid_i) assume (crisp_data_load_out_q[data_load_tag_i]);
      for (int t = 0; t < 16; t++)
        if (crisp_data_load_out_q[t] && crisp_data_load_age_q[t] >= 3'd3)
          assume (data_load_rvalid_i && data_load_tag_i == 4'(t));
    end
  end

  // CRISP grant_latency data_store 0: a raised request is accepted within 0 cycles
  logic [0:0] crisp_data_store_gwait_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) crisp_data_store_gwait_q <= '0;
    else if (data_store_req_o && !data_store_gnt_i) crisp_data_store_gwait_q <= crisp_data_store_gwait_q + 1'd1;
    else crisp_data_store_gwait_q <= '0;
  end
  always_comb begin
    if (rst_ni && data_store_req_o && crisp_data_store_gwait_q >= 1'd0) assume (data_store_gnt_i);
  end

  // CRISP response_latency data_store 3: every accepted request (tag data_store_tag_o) is
  // answered 1..3 cycles after acceptance; responses only for outstanding tags
  logic [15:0] crisp_data_store_out_q;
  logic [2:0] crisp_data_store_age_q [16];
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      crisp_data_store_out_q <= '0;
      for (int t = 0; t < 16; t++) crisp_data_store_age_q[t] <= '0;
    end else begin
      for (int t = 0; t < 16; t++) begin
        if ((data_store_req_o && data_store_gnt_i) && data_store_tag_o == 4'(t)) begin
          crisp_data_store_out_q[t] <= 1'b1;
          crisp_data_store_age_q[t] <= 3'd1;
        end else if ((data_store_rvalid_i && data_store_rready_o) && data_store_tag_i == 4'(t)) begin
          crisp_data_store_out_q[t] <= 1'b0;
          crisp_data_store_age_q[t] <= '0;
        end else if (crisp_data_store_out_q[t] && crisp_data_store_age_q[t] < 3'd3) begin
          crisp_data_store_age_q[t] <= crisp_data_store_age_q[t] + 3'd1;
        end
      end
    end
  end
  always_comb begin
    if (rst_ni) begin
      if (data_store_rvalid_i) assume (crisp_data_store_out_q[data_store_tag_i]);
      for (int t = 0; t < 16; t++)
        if (crisp_data_store_out_q[t] && crisp_data_store_age_q[t] >= 3'd3)
          assume (data_store_rvalid_i && data_store_tag_i == 4'(t));
    end
  end
