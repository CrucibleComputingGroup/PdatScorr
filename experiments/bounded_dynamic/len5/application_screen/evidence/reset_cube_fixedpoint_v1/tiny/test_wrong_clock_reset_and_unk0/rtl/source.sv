module Tiny(input clk_i,other_clk,rst_ni,other_rst,d, output reg a,b,c,e,f,g);
      always @(posedge clk_i or negedge rst_ni) if(!rst_ni) a<=0;else a<=a;
      always @(negedge clk_i or negedge rst_ni) if(!rst_ni) b<=0;else b<=b;
      always @(posedge other_clk or negedge rst_ni) if(!rst_ni) c<=0;else c<=c;
      always @(posedge clk_i or negedge other_rst) if(!other_rst) e<=0;else e<=e;
      always @(posedge clk_i or posedge rst_ni) if(rst_ni) f<=0;else f<=f;
      always @(posedge clk_i or negedge rst_ni) if(!rst_ni) g<=1'bx;else g<=g;
      endmodule