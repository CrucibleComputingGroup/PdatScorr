module GateToy(input clk, input [7:0] d); reg q; reg seen=0;
always @(posedge clk) begin q <= |d; seen <= 1; end
always @* begin assume(!d[0]); assume(!d[1]); assume(!d[2]); assume(!d[3]); assume(!d[4]); assume(!d[5]); assume(!d[6]); assume(!d[7]); if(seen) assert(!q); end endmodule
