module Tiny(input clk_i,rst_ni,flush, output reg q);
      wire x_or_hold=flush?1'bx:q;
      always @(posedge clk_i or negedge rst_ni) if(!rst_ni) q<=0; else q<=flush?1'b0:x_or_hold;
      endmodule