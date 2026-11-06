
  // ========================================
  // Auto-generated instruction constraints
  // Target core: rocket (rv32)
  // Inject into: rocket_synth_wrapper.core
  // Location: Rocket core - instruction fetch/decode
  // ========================================

  // V2: AIG-based per-instruction field constraints
  // Allowed instruction set: 22 instructions

  // Extract register fields
  wire [4:0] instr_rd = io_imem_resp_bits_data[11:7];
  wire [4:0] instr_rs1 = io_imem_resp_bits_data[19:15];
  wire [4:0] instr_rs2 = io_imem_resp_bits_data[24:20];

  always_comb begin
    assume (
      (((io_imem_resp_bits_data[31:0] & 32'hfe00707f) == 32'h00000033))  // ADD
      || (((io_imem_resp_bits_data[31:0] & 32'h0000707f) == 32'h00000013))  // ADDI
      || (((io_imem_resp_bits_data[31:0] & 32'h0000007f) == 32'h00000017))  // AUIPC
      || (((io_imem_resp_bits_data[31:0] & 32'h0000707f) == 32'h00000063))  // BEQ
      || (((io_imem_resp_bits_data[31:0] & 32'h0000707f) == 32'h00005063))  // BGE
      || (((io_imem_resp_bits_data[31:0] & 32'h0000707f) == 32'h00004063))  // BLT
      || (((io_imem_resp_bits_data[31:0] & 32'h0000707f) == 32'h00001063))  // BNE
      || (((io_imem_resp_bits_data[31:0] & 32'hffffffff) == 32'h00100073))  // EBREAK
      || (((io_imem_resp_bits_data[31:0] & 32'hffffffff) == 32'h00000073))  // ECALL
      || (((io_imem_resp_bits_data[31:0] & 32'h0000707f) == 32'h0000000f))  // FENCE
      || (((io_imem_resp_bits_data[31:0] & 32'h0000007f) == 32'h0000006f))  // JAL
      || (((io_imem_resp_bits_data[31:0] & 32'h0000707f) == 32'h00000067))  // JALR
      || (((io_imem_resp_bits_data[31:0] & 32'h0000707f) == 32'h00004003))  // LBU
      || (((io_imem_resp_bits_data[31:0] & 32'h0000007f) == 32'h00000037))  // LUI
      || (((io_imem_resp_bits_data[31:0] & 32'h0000707f) == 32'h00002003))  // LW
      || (((io_imem_resp_bits_data[31:0] & 32'hfe00707f) == 32'h00006033))  // OR
      || (((io_imem_resp_bits_data[31:0] & 32'h0000707f) == 32'h00000023))  // SB
      || (((io_imem_resp_bits_data[31:0] & 32'h0000707f) == 32'h00001023))  // SH
      || (((io_imem_resp_bits_data[31:0] & 32'h0000707f) == 32'h00003013))  // SLTIU
      || (((io_imem_resp_bits_data[31:0] & 32'hfe00707f) == 32'h40000033))  // SUB
      || (((io_imem_resp_bits_data[31:0] & 32'h0000707f) == 32'h00002023))  // SW
      || (((io_imem_resp_bits_data[31:0] & 32'h0000707f) == 32'h00004013))  // XORI
    );
  end
