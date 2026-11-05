module GateToy(input clk, input d);
reg q; always @(posedge clk) q <= 0;
always @* begin assume(!d); assert(!q); end
endmodule
