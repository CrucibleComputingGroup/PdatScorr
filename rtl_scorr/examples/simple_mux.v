// Simple example to test RTL-level scorr
// Mux that always selects one input (when enable=0)

module simple_mux (
    input wire clk,
    input wire rst,
    input wire enable,       // Constraint: assume(enable == 0)
    input wire [31:0] data_a,
    input wire [31:0] data_b,
    output reg [31:0] result
);

    // This mux should be proven equivalent to just data_a
    // when enable is constrained to 0
    always @(posedge clk or posedge rst) begin
        if (rst) begin
            result <= 32'h0;
        end else begin
            result <= enable ? data_b : data_a;
        end
    end

    // Constraint: enable is always 0
    // expect: result ≡ data_a (data_b path unused)
    always @(*) begin
        assume(enable == 1'b0);
    end

endmodule
