module Tiny(input clk, input [3:0] step);
reg [3:0] q = 4'd10;
always @* assume(step == 0 || step == 2);
always @(posedge clk) q <= q + step;
always @* assert(q[0] == 0);
endmodule
