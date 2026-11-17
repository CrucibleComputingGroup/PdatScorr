// Multiply/Divide Unit for RV32M extension
// Combinational implementation (suitable for single-cycle core)
// Supports conditional generation for RISSP-style additive approach
//
// Corrected version for the RISSP comparison (Table 1):
//  - MULH and MULHSU are implemented (the earlier version returned 0 for them),
//  - DIV and REM are signed (the earlier version computed them unsigned),
//  - the operation is decoded with explicit comparisons: the SystemVerilog front end
//    used by the flow (Synlig 2d838edc9) reads a two-value item of a `case (op) inside`
//    statement as a range and drops the top bit of its sized constants, which left the
//    divider of the earlier version unreachable.
module RiscvSingleCycle_mdu #(
    parameter bit ENABLE_MUL = 1, // Enable multiply operations
    parameter bit ENABLE_DIV = 1 // Enable divide operations
) (
    input  var logic [3-1:0]  op    , // MDU operation selection
    input  var logic [32-1:0] a     , // Operand A (rs1)
    input  var logic [32-1:0] b     , // Operand B (rs2)
    output var logic [32-1:0] // MDU result
     result
);
    // MDU operation codes (matches funct3 encoding)
    localparam logic [3-1:0] OP_MUL    = 3'b000; // MUL: multiply low 32 bits
    localparam logic [3-1:0] OP_MULH   = 3'b001; // MULH: multiply high (signed x signed)
    localparam logic [3-1:0] OP_MULHSU = 3'b010; // MULHSU: multiply high (signed x unsigned)
    localparam logic [3-1:0] OP_MULHU  = 3'b011; // MULHU: multiply high (unsigned x unsigned)
    localparam logic [3-1:0] OP_DIV    = 3'b100; // DIV: signed divide
    localparam logic [3-1:0] OP_DIVU   = 3'b101; // DIVU: unsigned divide
    localparam logic [3-1:0] OP_REM    = 3'b110; // REM: signed remainder
    localparam logic [3-1:0] OP_REMU   = 3'b111; // REMU: unsigned remainder

    logic [32-1:0] mdu_result;
    logic [32-1:0] mul_result;
    logic [32-1:0] div_result;

    // Conditional generate for multiplier
    if (ENABLE_MUL) begin :mul_gen
        // One unsigned 32x32 multiplier serves all four instructions. The high word of a
        // signed product is the unsigned high word minus b when a is negative and minus a
        // when b is negative (modulo 2^32).
        logic [64-1:0] mul_full;
        logic          a_signed_op;
        logic          b_signed_op;
        logic [32-1:0] corr_a;
        logic [32-1:0] corr_b;
        logic [32-1:0] mul_high;

        always_comb mul_full    = {32'h0, a} * {32'h0, b};
        always_comb a_signed_op = (op == OP_MULH) || (op == OP_MULHSU);
        always_comb b_signed_op = (op == OP_MULH);
        always_comb corr_a      = (((a_signed_op && a[31])) ? ( b ) : ( 32'h0 ));
        always_comb corr_b      = (((b_signed_op && b[31])) ? ( a ) : ( 32'h0 ));
        always_comb mul_high    = mul_full[63:32] - corr_a - corr_b;
        always_comb mul_result  = (((op == OP_MUL)) ? ( mul_full[31:0] ) : ( mul_high ));
    end else begin :mul_gen
        always_comb mul_result = 32'h0;
    end

    // Conditional generate for divider
    if (ENABLE_DIV) begin :div_gen
        // One unsigned divider serves all four instructions: signed operands are divided
        // by magnitude and the signs are restored afterwards.
        logic          div_signed ;
        logic          is_rem     ;
        logic          a_neg      ;
        logic          b_neg      ;
        logic [32-1:0] abs_a      ;
        logic [32-1:0] abs_b      ;
        logic [32-1:0] quotient_u ;
        logic [32-1:0] remainder_u;
        logic [32-1:0] quotient   ;
        logic [32-1:0] remainder  ;

        always_comb div_signed  = (op == OP_DIV) || (op == OP_REM);
        always_comb is_rem      = (op == OP_REM) || (op == OP_REMU);
        always_comb a_neg       = div_signed && a[31];
        always_comb b_neg       = div_signed && b[31];
        always_comb abs_a       = ((a_neg) ? ( ~a + 32'h1 ) : ( a ));
        always_comb abs_b       = ((b_neg) ? ( ~b + 32'h1 ) : ( b ));
        always_comb quotient_u  = abs_a / abs_b;
        always_comb remainder_u = abs_a % abs_b;
        always_comb quotient    = (((a_neg != b_neg)) ? ( ~quotient_u + 32'h1 ) : ( quotient_u ));
        always_comb remainder   = ((a_neg) ? ( ~remainder_u + 32'h1 ) : ( remainder_u ));

        always_comb begin
            if (b == 32'h0) begin
                // Division by zero: quotient is all ones, remainder is the dividend
                div_result = ((is_rem) ? ( a ) : ( 32'hFFFFFFFF ));
            end else begin
                div_result = ((is_rem) ? ( remainder ) : ( quotient ));
            end
        end
    end else begin :div_gen
        always_comb div_result = 32'h0;
    end

    // Select result based on operation: funct3[2] separates divide/remainder from multiply
    always_comb mdu_result = ((op[2]) ? ( div_result ) : ( mul_result ));

    always_comb result = mdu_result;
endmodule
