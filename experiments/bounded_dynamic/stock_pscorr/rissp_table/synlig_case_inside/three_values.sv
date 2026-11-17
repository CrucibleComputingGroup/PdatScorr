// Control: three values in one item. Elaborated correctly (op == 2, 6, 7).
module three_values (input logic [2:0] op, input logic [7:0] a, b, output logic [7:0] y);
  always_comb begin
    y = 8'h0;
    case (op) inside
      3'd2, 3'd6, 3'd7: y = a + b;
      default:          y = 8'h0;
    endcase
  end
endmodule
