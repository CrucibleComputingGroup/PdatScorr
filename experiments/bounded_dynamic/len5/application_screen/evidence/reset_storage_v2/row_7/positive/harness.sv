module ResetStorageProof(input [0:0] clk_i, input [0:0] rst_ni, input [0:0] insert_i, input [2:0] new_index_i, input [297:0] rs_inputs, input [141:0] other_state);
wire [219:0] row_q;
NativeRow dut(.clk_i(clk_i), .rst_ni(rst_ni), .insert_i(insert_i), .new_index_i(new_index_i), .rs_inputs(rs_inputs), .other_state(other_state), .row_q(row_q));
always @* begin
  if ($initstate) assume(!rst_ni);
  if (rst_ni) assume(!(insert_i && new_index_i == 3'd7));
  assert(row_q == 220'b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000);
end
endmodule
