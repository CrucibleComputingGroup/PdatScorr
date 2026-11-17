// Control: the expression form of inside. Elaborated correctly (op == 4, op == 5).
module inside_expr (input logic [2:0] op, input logic [7:0] a, b, output logic [7:0] y);
  always_comb begin
    if (op inside {3'd4, 3'd5}) y = a + b;
    else                        y = 8'h0;
  end
endmodule
