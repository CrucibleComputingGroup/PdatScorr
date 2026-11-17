// A value range with sized bounds in a case-inside statement.
// Expected: y = a + b when op is 4 or 5.
// Synlig 2d838edc9 drops the top bit of the bounds and compares op with 0 and 1.
module range (input logic [2:0] op, input logic [7:0] a, b, output logic [7:0] y);
  always_comb begin
    y = 8'h0;
    case (op) inside
      [3'd4:3'd5]: y = a + b;
      default:     y = 8'h0;
    endcase
  end
endmodule
