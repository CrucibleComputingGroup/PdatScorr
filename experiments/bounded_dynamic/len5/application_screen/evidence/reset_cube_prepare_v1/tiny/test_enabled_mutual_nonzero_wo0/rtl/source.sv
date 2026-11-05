module Tiny(input clk_i,rst_ni,en, output reg [1:0] a,b);
      always @(posedge clk_i or negedge rst_ni) if(!rst_ni) a<=2'b10; else if(en) a<=b;
      always @(posedge clk_i or negedge rst_ni) if(!rst_ni) b<=2'b10; else if(!en) b<=a;
      endmodule