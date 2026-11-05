module Tiny(input clk_i,rst_ni,output reg [3:0] a,b);
      always @(posedge clk_i or negedge rst_ni) if(!rst_ni) begin a<=9;b<=9;end
        else begin a<=b;b<=a;end endmodule