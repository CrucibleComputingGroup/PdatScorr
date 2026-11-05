module Tiny(input clk_i,rst_ni,d, output reg [63:0] q);
      always @(posedge clk_i or negedge rst_ni) if(!rst_ni) q<=0;else q<={q[63:1],d};
      endmodule