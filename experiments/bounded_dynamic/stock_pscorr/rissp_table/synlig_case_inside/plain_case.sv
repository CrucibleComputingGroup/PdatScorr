// Control: plain case with the same two values. Elaborated correctly (op == 4, op == 5).
module plain_case (input logic [2:0] op, input logic [7:0] a, b, output logic [7:0] y);
  always_comb begin
    y = 8'h0;
    case (op)
      3'd4, 3'd5: y = a + b;
      default:    y = 8'h0;
    endcase
  end
endmodule
