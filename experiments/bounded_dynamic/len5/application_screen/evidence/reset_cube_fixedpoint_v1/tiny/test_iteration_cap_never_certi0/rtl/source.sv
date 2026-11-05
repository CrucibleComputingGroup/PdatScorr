module Tiny(input clk_i,rst_ni,d,output reg a,b);
      always @(posedge clk_i or negedge rst_ni) if(!rst_ni) begin a<=0;b<=0;end
        else begin a<=d;b<=a;end endmodule