// Two values that are not neighbours.
// Expected: y = a + b when op is 9 or 12.
// Synlig 2d838edc9 reads the item as the range [9:12] and also matches 10 and 11.
module pair_gap (input logic [4:0] op, input logic [7:0] a, b, output logic [7:0] y);
  always_comb begin
    y = 8'h0;
    case (op) inside
      5'd9, 5'd12: y = a + b;
      default:     y = 8'h0;
    endcase
  end
endmodule
