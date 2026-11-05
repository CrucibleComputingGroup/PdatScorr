module Tiny(input clk);
reg [3:0] q;
always @(posedge clk) q <= q;
always @* assert(q == 0);
endmodule
