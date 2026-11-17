// The shape of the single-cycle core's divider: two items of two values each.
// Expected: y = a for op 6 or 7, y = b for op 4 or 5.
// Synlig 2d838edc9 compares op with 2 and 3 for the first item and with 0 and 1 for the
// second.
module two_pairs (input logic [2:0] op, input logic [7:0] a, b, output logic [7:0] y);
  always_comb begin
    y = 8'h0;
    case (op) inside
      3'd6, 3'd7: y = a;
      3'd4, 3'd5: y = b;
      default:    y = 8'h0;
    endcase
  end
endmodule
