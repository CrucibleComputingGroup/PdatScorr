
  // Pscorr reset semantics: reset is applied in the first cycle and is free afterwards
  logic pscorr_first_cycle_q = 1'b1;
  always_ff @(posedge clk_i) pscorr_first_cycle_q <= 1'b0;
  always_comb if (pscorr_first_cycle_q) assume (!rst_ni);
