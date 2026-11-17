// Control: one value per item. Elaborated correctly (op == 4, op == 5).
module single (input logic [2:0] op, input logic [7:0] a, b, output logic [7:0] y);
  always_comb begin
    y = 8'h0;
    case (op) inside
      3'd4:    y = a + b;
      3'd5:    y = a + b;
      default: y = 8'h0;
    endcase
  end
endmodule
