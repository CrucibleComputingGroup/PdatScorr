module EUProof(input [0:0] clk_i, input [0:0] rst_ni, input [0:0] decoded_high, input [1:0] controls, output [0:0] visible_high);
NativeEURegister dut(.clk_i(clk_i), .rst_ni(rst_ni), .decoded_high(decoded_high), .controls(controls), .visible_high(visible_high));
always @* begin
if ($initstate) assume(!rst_ni);
assume(decoded_high == 0);
assert(visible_high == 0);
end
endmodule
