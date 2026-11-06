
  // ========================================
  // Auto-generated instruction constraints
  // Target core: len5 (rv64)
  // Inject into: datapath.u_backend.u_issue_stage
  // Location: LEN5 issue stage - ISA constraints on the issue decoder input
  // ========================================

  // V2: AIG-based per-instruction field constraints
  // Allowed instruction set: 27 instructions

  // Extract register fields
  wire [4:0] instr_rd = pscorr_isa_word[11:7];
  wire [4:0] instr_rs1 = pscorr_isa_word[19:15];
  wire [4:0] instr_rs2 = pscorr_isa_word[24:20];

  always_comb begin
    assume (!rst_ni || (
      (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h00000033))  // ADD
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00000013))  // ADDI
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h0000001b))  // ADDIW
      || (((pscorr_isa_word[31:0] & 32'h0000007f) == 32'h00000017))  // AUIPC
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00000063))  // BEQ
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00005063))  // BGE
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00004063))  // BLT
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00006063))  // BLTU
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00001063))  // BNE
      || (((pscorr_isa_word[31:0] & 32'h0000007f) == 32'h0000006f))  // JAL
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00000067))  // JALR
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00004003))  // LBU
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00003003))  // LD
      || (((pscorr_isa_word[31:0] & 32'h0000007f) == 32'h00000037))  // LUI
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00002003))  // LW
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h02000033))  // MUL
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h00006033))  // OR
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00000023))  // SB
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00003023))  // SD
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00001023))  // SH
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h00001013))  // SLLI
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00003013))  // SLTIU
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h00003033))  // SLTU
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h00005013))  // SRLI
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h40000033))  // SUB
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00002023))  // SW
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00004013))  // XORI
    ));
  end
