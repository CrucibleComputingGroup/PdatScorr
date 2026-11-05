module Tiny(input clk);
(* anyconst *) reg [3:0] value;
reg [3:0] previous;
reg sampled = 0;
always @(posedge clk) begin previous <= value; sampled <= 1; end
always @* if(sampled) assert(value == previous);
endmodule
