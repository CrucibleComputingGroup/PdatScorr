module Ref(input s,d,output reg y); always @* y = s ? 1'bx : d; endmodule
