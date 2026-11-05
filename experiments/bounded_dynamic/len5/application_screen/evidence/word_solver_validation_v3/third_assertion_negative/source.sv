module Tiny(input clk,input [7:0] guarded);
reg [7:0] q = 8'ha5;
always @* begin
 assume(guarded[0] == 1); assume(guarded[1] == 0);
 assume(guarded[2] == 1); assume(guarded[3] == 0);
 assume(guarded[4] == 0); assume(guarded[5] == 1);
 assume(guarded[6] == 0); assume(guarded[7] == 1);
 assert(q[0] == 1); assert(q[1] == 0); assert(q == 0);
end
always @(posedge clk) q <= guarded;
endmodule
