module Tiny(input clk_i,rst_ni,we,addr,d, output reg q);
      reg mem[0:1];
      always @(posedge clk_i) if(we) mem[addr]<=d;
      always @(posedge clk_i or negedge rst_ni) if(!rst_ni) q<=0;else q<=mem[addr];
      endmodule