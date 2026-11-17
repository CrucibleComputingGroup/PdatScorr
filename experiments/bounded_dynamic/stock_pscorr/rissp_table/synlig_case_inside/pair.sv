// Two values in one item of a case-inside statement.
// Expected: y = a + b when op is 4 or 5.
// Synlig 2d838edc9 reads the item as the range [4:5] and drops the top bit of the sized
// constants, so it compares op with 0 and 1.
module pair (input logic [2:0] op, input logic [7:0] a, b, output logic [7:0] y);
  always_comb begin
    y = 8'h0;
    case (op) inside
      3'd4, 3'd5: y = a + b;
      default:    y = 8'h0;
    endcase
  end
endmodule
