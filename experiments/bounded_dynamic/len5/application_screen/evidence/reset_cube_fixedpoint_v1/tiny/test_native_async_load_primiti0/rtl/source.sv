module AsyncLoad(input clk_i,rst_ni, input [1:0] initial_value,d,
        output reg [1:0] q);
      always @(posedge clk_i or negedge rst_ni) if(!rst_ni) q<=initial_value;else q<=d;
      endmodule
      module Tiny(input clk_i,rst_ni, output [1:0] a,b);
      AsyncLoad first(clk_i,rst_ni,2'b01,b,a);
      AsyncLoad second(clk_i,rst_ni,2'b01,a,b);
      endmodule