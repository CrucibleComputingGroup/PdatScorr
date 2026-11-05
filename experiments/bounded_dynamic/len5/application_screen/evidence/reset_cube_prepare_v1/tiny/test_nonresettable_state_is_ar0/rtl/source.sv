module Tiny(input clk_i,rst_ni,d, output reg a,q);
      always @(posedge clk_i) a<=d;
      always @(posedge clk_i or negedge rst_ni) if(!rst_ni) q<=0;else q<=a;
      endmodule