
  // Pscorr: the word entering the issue decoder from a valid issue-queue entry without a
  // fetch exception (a NOP otherwise); the word the CRISP ISA assumptions constrain.
  wire [31:0] pscorr_isa_word = (iq_cu_valid && !iq_data_out.except_raised) ? iq_data_out.instruction : 32'h00000013;

  // ========================================
  // Auto-generated instruction constraints
  // Target core: len5 (rv64)
  // Inject into: datapath.u_backend.u_issue_stage
  // Location: LEN5 issue stage - ISA constraints on the issue decoder input
  // ========================================

  // V2: AIG-based per-instruction field constraints
  // Allowed instruction set: 65 instructions

  // Extract register fields
  wire [4:0] instr_rd = pscorr_isa_word[11:7];
  wire [4:0] instr_rs1 = pscorr_isa_word[19:15];
  wire [4:0] instr_rs2 = pscorr_isa_word[24:20];

  always_comb begin
    assume (!rst_ni || (
      (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h00000033))  // ADD
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00000013))  // ADDI
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h0000001b))  // ADDIW
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h0000003b))  // ADDW
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h00007033))  // AND
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00007013))  // ANDI
      || (((pscorr_isa_word[31:0] & 32'h0000007f) == 32'h00000017))  // AUIPC
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00000063))  // BEQ
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00005063))  // BGE
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00007063))  // BGEU
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00004063))  // BLT
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00006063))  // BLTU
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00001063))  // BNE
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h02004033))  // DIV
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h02005033))  // DIVU
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h0200503b))  // DIVUW
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h0200403b))  // DIVW
      || (((pscorr_isa_word[31:0] & 32'hffffffff) == 32'h00100073))  // EBREAK
      || (((pscorr_isa_word[31:0] & 32'hffffffff) == 32'h00000073))  // ECALL
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h0000000f))  // FENCE
      || (((pscorr_isa_word[31:0] & 32'h0000007f) == 32'h0000006f))  // JAL
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00000067))  // JALR
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00000003))  // LB
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00004003))  // LBU
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00003003))  // LD
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00001003))  // LH
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00005003))  // LHU
      || (((pscorr_isa_word[31:0] & 32'h0000007f) == 32'h00000037))  // LUI
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00002003))  // LW
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00006003))  // LWU
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h02000033))  // MUL
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h02001033))  // MULH
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h02002033))  // MULHSU
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h02003033))  // MULHU
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h0200003b))  // MULW
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h00006033))  // OR
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00006013))  // ORI
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h02006033))  // REM
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h02007033))  // REMU
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h0200703b))  // REMUW
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h0200603b))  // REMW
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00000023))  // SB
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00003023))  // SD
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00001023))  // SH
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h00001033))  // SLL
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h00001013))  // SLLI
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h0000101b))  // SLLIW
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h0000103b))  // SLLW
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h00002033))  // SLT
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00002013))  // SLTI
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00003013))  // SLTIU
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h00003033))  // SLTU
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h40005033))  // SRA
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h40005013))  // SRAI
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h4000501b))  // SRAIW
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h4000503b))  // SRAW
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h00005033))  // SRL
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h00005013))  // SRLI
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h0000501b))  // SRLIW
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h0000503b))  // SRLW
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h40000033))  // SUB
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h4000003b))  // SUBW
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00002023))  // SW
      || (((pscorr_isa_word[31:0] & 32'hfe00707f) == 32'h00004033))  // XOR
      || (((pscorr_isa_word[31:0] & 32'h0000707f) == 32'h00004013))  // XORI
    ));
  end
