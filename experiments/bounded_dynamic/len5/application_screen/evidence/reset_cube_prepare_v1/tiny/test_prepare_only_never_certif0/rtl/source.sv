module Tiny(input clk_i,rst_ni, output reg q);
      always @(posedge clk_i or negedge rst_ni) if(!rst_ni) q<=0;else q<=q;
      endmodule