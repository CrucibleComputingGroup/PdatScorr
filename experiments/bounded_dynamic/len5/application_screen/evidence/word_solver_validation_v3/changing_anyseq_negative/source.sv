module Tiny(input clk);
reg [3:0] q = 0;
(* anyseq *) reg [3:0] arbitrary_value;
always @(posedge clk) q <= arbitrary_value;
always @* assert(q[0] == 0);
endmodule
