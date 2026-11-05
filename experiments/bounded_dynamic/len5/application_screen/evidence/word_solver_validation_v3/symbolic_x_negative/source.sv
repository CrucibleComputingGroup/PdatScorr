module Tiny(input clk);
wire [3:0] x = 4'bxxxx;
always @* assert(x == 0);
endmodule
