
  // ========================================
  // Auto-generated instruction constraints
  // Target core: len5 (rv64)
  // Inject into: datapath
  // Location: LEN5 datapath - ISA constraints on the instruction-memory read data
  // ========================================

  // V2: AIG-based per-instruction field constraints
  // Allowed instruction set: 35 instructions

  // Extract register fields
  wire [4:0] instr_rd = instr_rdata_i[11:7];
  wire [4:0] instr_rs1 = instr_rdata_i[19:15];
  wire [4:0] instr_rs2 = instr_rdata_i[24:20];

  always_comb begin
    assume (!rst_ni || (
      (((instr_rdata_i[31:0] & 32'hfe00707f) == 32'h00000033))  // ADD
      || (((instr_rdata_i[31:0] & 32'h0000707f) == 32'h00000013))  // ADDI
      || (((instr_rdata_i[31:0] & 32'h0000707f) == 32'h0000001b))  // ADDIW
      || (((instr_rdata_i[31:0] & 32'hfe00707f) == 32'h0000003b))  // ADDW
      || (((instr_rdata_i[31:0] & 32'h0000007f) == 32'h00000017))  // AUIPC
      || (((instr_rdata_i[31:0] & 32'h0000707f) == 32'h00000063))  // BEQ
      || (((instr_rdata_i[31:0] & 32'h0000707f) == 32'h00005063))  // BGE
      || (((instr_rdata_i[31:0] & 32'h0000707f) == 32'h00006063))  // BLTU
      || (((instr_rdata_i[31:0] & 32'h0000707f) == 32'h00001063))  // BNE
      || (((instr_rdata_i[31:0] & 32'h0000007f) == 32'h0000006f))  // JAL
      || (((instr_rdata_i[31:0] & 32'h0000707f) == 32'h00000067))  // JALR
      || (((instr_rdata_i[31:0] & 32'h0000707f) == 32'h00004003))  // LBU
      || (((instr_rdata_i[31:0] & 32'h0000707f) == 32'h00003003))  // LD
      || (((instr_rdata_i[31:0] & 32'h0000707f) == 32'h00001003))  // LH
      || (((instr_rdata_i[31:0] & 32'h0000707f) == 32'h00005003))  // LHU
      || (((instr_rdata_i[31:0] & 32'h0000007f) == 32'h00000037))  // LUI
      || (((instr_rdata_i[31:0] & 32'h0000707f) == 32'h00002003))  // LW
      || (((instr_rdata_i[31:0] & 32'hfe00707f) == 32'h02000033))  // MUL
      || (((instr_rdata_i[31:0] & 32'hfe00707f) == 32'h0200003b))  // MULW
      || (((instr_rdata_i[31:0] & 32'h0000707f) == 32'h00000023))  // SB
      || (((instr_rdata_i[31:0] & 32'h0000707f) == 32'h00003023))  // SD
      || (((instr_rdata_i[31:0] & 32'h0000707f) == 32'h00001023))  // SH
      || (((instr_rdata_i[31:0] & 32'hfe00707f) == 32'h00001013))  // SLLI
      || (((instr_rdata_i[31:0] & 32'hfe00707f) == 32'h0000101b))  // SLLIW
      || (((instr_rdata_i[31:0] & 32'h0000707f) == 32'h00003013))  // SLTIU
      || (((instr_rdata_i[31:0] & 32'hfe00707f) == 32'h00003033))  // SLTU
      || (((instr_rdata_i[31:0] & 32'hfe00707f) == 32'h40005033))  // SRA
      || (((instr_rdata_i[31:0] & 32'hfe00707f) == 32'h40005013))  // SRAI
      || (((instr_rdata_i[31:0] & 32'hfe00707f) == 32'h4000501b))  // SRAIW
      || (((instr_rdata_i[31:0] & 32'hfe00707f) == 32'h4000503b))  // SRAW
      || (((instr_rdata_i[31:0] & 32'hfe00707f) == 32'h00005013))  // SRLI
      || (((instr_rdata_i[31:0] & 32'hfe00707f) == 32'h40000033))  // SUB
      || (((instr_rdata_i[31:0] & 32'hfe00707f) == 32'h4000003b))  // SUBW
      || (((instr_rdata_i[31:0] & 32'h0000707f) == 32'h00002023))  // SW
      || (((instr_rdata_i[31:0] & 32'h0000707f) == 32'h00004013))  // XORI
    ));
  end

  // Pscorr reset semantics: reset is applied in the first cycle and is free afterwards
  logic pscorr_first_cycle_q = 1'b1;
  always_ff @(posedge clk_i) pscorr_first_cycle_q <= 1'b0;
  always_comb if (pscorr_first_cycle_q) assume (!rst_ni);
