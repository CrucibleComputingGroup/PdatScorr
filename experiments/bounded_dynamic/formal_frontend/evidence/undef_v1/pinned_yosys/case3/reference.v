module Ref(input s,d,output reg y); always @* case(s) 1'b0:y=d; default:y=1'bx; endcase endmodule
