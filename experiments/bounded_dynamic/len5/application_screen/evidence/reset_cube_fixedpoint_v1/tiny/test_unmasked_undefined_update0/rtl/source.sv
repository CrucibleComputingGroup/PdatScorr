module Tiny(input clk_i,rst_ni,en, output reg q);
      always @(posedge clk_i or negedge rst_ni) if(!rst_ni) q<=0; else q<=en?1'bx:1'b0;
      endmodule