module Tiny(input clk,rst_n,input [3:0] step);
reg [3:0] q;
always @* begin
 if ($initstate) assume(!rst_n);
 assume(step == 0 || step == 2);
 if (rst_n) assert(q[0] == 0);
end
always @(posedge clk) if(!rst_n) q <= 6; else q <= q + step;
endmodule
