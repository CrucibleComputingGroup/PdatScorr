// The expression form of inside with a value range.
// Expected: y = a + b when op is 4 or 5.
// Synlig 2d838edc9 matches only the lower bound (op == 4).
module inside_range_expr (input logic [2:0] op, input logic [7:0] a, b, output logic [7:0] y);
  always_comb begin
    if (op inside {[3'd4:3'd5]}) y = a + b;
    else                         y = 8'h0;
  end
endmodule
