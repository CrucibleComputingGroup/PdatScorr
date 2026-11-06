
  // ========================================
  // Auto-generated instruction constraints
  // Target core: len5 (rv64)
  // Inject into: datapath
  // Location: LEN5 datapath - ISA constraints on the instruction-memory read data
  // ========================================

  // V2: AIG-based per-instruction field constraints
  // Allowed instruction set: 27 instructions

  // Extract register fields
  wire [4:0] instr_rd = instr_rdata_i[11:7];
  wire [4:0] instr_rs1 = instr_rdata_i[19:15];
  wire [4:0] instr_rs2 = instr_rdata_i[24:20];

  always_comb begin
    assume (!rst_ni || (
      (((instr_rdata_i[31:0] & 32'hfe00707f) == 32'h00000033))  // ADD
      || (((instr_rdata_i[31:0] & 32'h0000707f) == 32'h00000013))  // ADDI
      || (((instr_rdata_i[31:0] & 32'h0000707f) == 32'h0000001b))  // ADDIW
      || (((instr_rdata_i[31:0] & 32'hfe00707f) == 32'h00007033))  // AND
      || (((instr_rdata_i[31:0] & 32'h0000707f) == 32'h00007013))  // ANDI
      || (((instr_rdata_i[31:0] & 32'h0000007f) == 32'h00000017))  // AUIPC
      || (((instr_rdata_i[31:0] & 32'h0000707f) == 32'h00000063))  // BEQ
      || (((instr_rdata_i[31:0] & 32'h0000707f) == 32'h00005063))  // BGE
      || (((instr_rdata_i[31:0] & 32'h0000707f) == 32'h00006063))  // BLTU
      || (((instr_rdata_i[31:0] & 32'h0000707f) == 32'h00001063))  // BNE
      || (((instr_rdata_i[31:0] & 32'h0000707f) == 32'h00000067))  // JALR
      || (((instr_rdata_i[31:0] & 32'h0000707f) == 32'h00004003))  // LBU
      || (((instr_rdata_i[31:0] & 32'h0000707f) == 32'h00003003))  // LD
      || (((instr_rdata_i[31:0] & 32'h0000007f) == 32'h00000037))  // LUI
      || (((instr_rdata_i[31:0] & 32'hfe00707f) == 32'h02000033))  // MUL
      || (((instr_rdata_i[31:0] & 32'hfe00707f) == 32'h02003033))  // MULHU
      || (((instr_rdata_i[31:0] & 32'hfe00707f) == 32'h00006033))  // OR
      || (((instr_rdata_i[31:0] & 32'h0000707f) == 32'h00000023))  // SB
      || (((instr_rdata_i[31:0] & 32'h0000707f) == 32'h00003023))  // SD
      || (((instr_rdata_i[31:0] & 32'hfe00707f) == 32'h00001013))  // SLLI
      || (((instr_rdata_i[31:0] & 32'h0000707f) == 32'h00003013))  // SLTIU
      || (((instr_rdata_i[31:0] & 32'hfe00707f) == 32'h00003033))  // SLTU
      || (((instr_rdata_i[31:0] & 32'hfe00707f) == 32'h40005013))  // SRAI
      || (((instr_rdata_i[31:0] & 32'hfe00707f) == 32'h00005013))  // SRLI
      || (((instr_rdata_i[31:0] & 32'hfe00707f) == 32'h40000033))  // SUB
      || (((instr_rdata_i[31:0] & 32'hfe00707f) == 32'h00004033))  // XOR
      || (((instr_rdata_i[31:0] & 32'h0000707f) == 32'h00004013))  // XORI
    ));
  end
