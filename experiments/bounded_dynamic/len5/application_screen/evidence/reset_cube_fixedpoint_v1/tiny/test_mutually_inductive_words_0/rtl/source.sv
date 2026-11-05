module Tiny(input clk_i,rst_ni, output reg [2:0] a,b);
      always @(posedge clk_i or negedge rst_ni) if(!rst_ni) begin a<=3'b101;b<=3'b101;end
        else begin a<=b;b<=a;end endmodule