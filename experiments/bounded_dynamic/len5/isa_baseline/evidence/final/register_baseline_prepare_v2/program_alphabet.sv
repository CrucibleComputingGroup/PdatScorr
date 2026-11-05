module TemporalMiter(input [0:0] clk_i, input [0:0] rst_ni, input [0:0] comm_valid_i, input [4:0] comm_rd_idx_i, input [63:0] comm_rd_value_i, input [4:0] issue_rs1_idx_i, input [4:0] issue_rs2_idx_i);
wire [63:0] a_issue_rs1_value_o;
wire [63:0] a_issue_rs2_value_o;
DecoderBase reference(.clk_i(clk_i), .rst_ni(rst_ni), .comm_valid_i(comm_valid_i), .comm_rd_idx_i(comm_rd_idx_i), .comm_rd_value_i(comm_rd_value_i), .issue_rs1_idx_i(issue_rs1_idx_i), .issue_rs2_idx_i(issue_rs2_idx_i), .issue_rs1_value_o(a_issue_rs1_value_o), .issue_rs2_value_o(a_issue_rs2_value_o));
wire [63:0] b_issue_rs1_value_o;
wire [63:0] b_issue_rs2_value_o;
DecoderCandidate candidate(.clk_i(clk_i), .rst_ni(rst_ni), .comm_valid_i(comm_valid_i), .comm_rd_idx_i(comm_rd_idx_i), .comm_rd_value_i(comm_rd_value_i), .issue_rs1_idx_i(issue_rs1_idx_i), .issue_rs2_idx_i(issue_rs2_idx_i), .issue_rs1_value_o(b_issue_rs1_value_o), .issue_rs2_value_o(b_issue_rs2_value_o));
always @* begin
  if ($initstate) assume(!rst_ni);
  assume((comm_rd_idx_i == 5'd0) || (comm_rd_idx_i == 5'd5) || (comm_rd_idx_i == 5'd8) || (comm_rd_idx_i == 5'd9) || (comm_rd_idx_i == 5'd10) || (comm_rd_idx_i == 5'd11) || (comm_rd_idx_i == 5'd18));
  assert(a_issue_rs1_value_o == b_issue_rs1_value_o);
  assert(a_issue_rs2_value_o == b_issue_rs2_value_o);
end
endmodule
