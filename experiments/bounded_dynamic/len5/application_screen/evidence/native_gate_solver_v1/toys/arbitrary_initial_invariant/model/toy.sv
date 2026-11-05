module GateToy(input clk, input d);
reg [1:0] q; reg previous; reg seen=0;
always @(posedge clk) begin q <= q+2; previous <= q[0]; seen <= 1; end
always @* if(seen) assert(q[0] == previous);
endmodule
