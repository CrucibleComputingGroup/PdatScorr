// ALU for RV32E
// Supports all integer arithmetic and logic operations
// Supports conditional generation for RISSP-style additive approach
//
// Corrected version for the RISSP comparison (Table 1): the adder that forms load and
// store addresses, LUI, AUIPC and JALR targets is always present. ENABLE_ADDER now
// switches only the logic that the add/compare instructions need beyond it (SUB, SLT,
// SLTU). In the earlier version ENABLE_ADDER = 0 tied the adder output to zero, so a
// core without the add instructions could not address memory.
module RiscvSingleCycle_alu #(
    parameter bit ENABLE_ADDER   = 1, // Enable subtract/compare (SUB/SLT/SLTU)
    parameter bit ENABLE_SHIFTER = 1 // Enable barrel shifter (SLL/SRL/SRA)
) (
    input  var logic [4-1:0]  op    ,
    input  var logic [32-1:0] a     ,
    input  var logic [32-1:0] b     ,
    output var logic [32-1:0] result,
    output var logic          zero  
);
    // ALU operation codes
    localparam logic [4-1:0] OP_ADD  = 4'b0000;
    localparam logic [4-1:0] OP_SUB  = 4'b0001;
    localparam logic [4-1:0] OP_SLL  = 4'b0010;
    localparam logic [4-1:0] OP_SLT  = 4'b0011;
    localparam logic [4-1:0] OP_SLTU = 4'b0100;
    localparam logic [4-1:0] OP_XOR  = 4'b0101;
    localparam logic [4-1:0] OP_SRL  = 4'b0110;
    localparam logic [4-1:0] OP_SRA  = 4'b0111;
    localparam logic [4-1:0] OP_OR   = 4'b1000;
    localparam logic [4-1:0] OP_AND  = 4'b1001;

    logic        [32-1:0] alu_result    ;
    logic        [32-1:0] add_result    ;
    logic        [32-1:0] adder_result  ;
    logic        [32-1:0] shifter_result;
    logic signed [32-1:0] a_signed      ;
    logic signed [32-1:0] b_signed      ;

    always_comb a_signed = a;
    always_comb b_signed = b;

    // Address adder (loads, stores, LUI, AUIPC, JALR) and ADD/ADDI: always present
    always_comb add_result = a + b;

    // Conditional generate for subtract/compare
    if (ENABLE_ADDER) begin :adder_gen
        logic signed [33-1:0] sub_result; // 33-bit for overflow detection

        always_comb begin
            adder_result = 32'h0;
            sub_result   = 33'h0;

            if (op == OP_SUB) begin
                adder_result = a - b;
            end else if (op == OP_SLT) begin
                // Set if less than (signed) - use subtraction
                sub_result   = {a_signed[31], a_signed} - {b_signed[31], b_signed};
                adder_result = ((sub_result[32]) ? ( 32'h1 ) : ( 32'h0 ));
            end else if (op == OP_SLTU) begin
                // Set if less than (unsigned)
                adder_result = (((a < b)) ? ( 32'h1 ) : ( 32'h0 ));
            end
        end
    end else begin :adder_gen
        always_comb adder_result = 32'h0;
    end

    // Conditional generate for shifter
    if (ENABLE_SHIFTER) begin :shifter_gen
        always_comb begin
            shifter_result = 32'h0;
            if (op == OP_SLL) begin
                shifter_result = a << b[4:0];
            end else if (op == OP_SRL) begin
                shifter_result = a >> b[4:0];
            end else if (op == OP_SRA) begin
                shifter_result = a_signed >>> b[4:0];
            end
        end
    end else begin :shifter_gen
        always_comb shifter_result = 32'h0;
    end

    // Combine results
    always_comb begin
        if (op == OP_ADD) begin
            alu_result = add_result;
        end else if ((op == OP_SUB) || (op == OP_SLT) || (op == OP_SLTU)) begin
            alu_result = adder_result;
        end else if ((op == OP_SLL) || (op == OP_SRL) || (op == OP_SRA)) begin
            alu_result = shifter_result;
        end else if (op == OP_XOR) begin
            alu_result = a ^ b;
        end else if (op == OP_OR) begin
            alu_result = a | b;
        end else if (op == OP_AND) begin
            alu_result = a & b;
        end else begin
            alu_result = 32'h0;
        end
    end

    always_comb result = alu_result;
    always_comb zero   = alu_result == 0;
endmodule
