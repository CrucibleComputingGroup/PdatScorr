// Minimal wrapper to connect ibex_core with ibex_register_file_ff
// Avoids the PRIM infrastructure complexity in ibex_top

module ibex_core_with_rf import ibex_pkg::*; #(
  // Core parameters - match ibex_core defaults
  parameter bit                     PMPEnable        = 1'b0,
  parameter int unsigned            PMPGranularity   = 0,
  parameter int unsigned            PMPNumRegions    = 4,
  parameter ibex_pkg::pmp_cfg_t     PMPRstCfg[16]    = ibex_pkg::PmpCfgRst,
  parameter logic [33:0]            PMPRstAddr[16]   = ibex_pkg::PmpAddrRst,
  parameter ibex_pkg::pmp_mseccfg_t PMPRstMsecCfg    = ibex_pkg::PmpMseccfgRst,
  parameter int unsigned            MHPMCounterNum   = 0,
  parameter int unsigned            MHPMCounterWidth = 40,
  parameter bit                     RV32E            = 1'b0,
  parameter rv32m_e                 RV32M            = RV32MFast,
  parameter rv32b_e                 RV32B            = RV32BNone,
  parameter bit                     BranchTargetALU  = 1'b0,
  parameter bit                     WritebackStage   = 1'b0,
  parameter bit                     ICache           = 1'b0,
  parameter bit                     ICacheECC        = 1'b0,
  parameter int unsigned            BusSizeECC       = BUS_SIZE,
  parameter int unsigned            TagSizeECC       = IC_TAG_SIZE,
  parameter int unsigned            LineSizeECC      = IC_LINE_SIZE,
  parameter bit                     BranchPredictor  = 1'b0,
  parameter bit                     DbgTriggerEn     = 1'b0,
  parameter int unsigned            DbgHwBreakNum    = 1,
  parameter bit                     ResetAll         = 1'b0,
  parameter lfsr_seed_t             RndCnstLfsrSeed  = RndCnstLfsrSeedDefault,
  parameter lfsr_perm_t             RndCnstLfsrPerm  = RndCnstLfsrPermDefault,
  parameter bit                     SecureIbex       = 1'b0,
  parameter bit                     DummyInstructions= 1'b0,
  parameter bit                     RegFileECC       = 1'b0,
  parameter int unsigned            RegFileDataWidth = 32,
  parameter bit                     MemECC           = 1'b0,
  parameter int unsigned            MemDataWidth     = MemECC ? 32 + 7 : 32,
  parameter int unsigned            DmBaseAddr       = 32'h1A110000,
  parameter int unsigned            DmAddrMask       = 32'h00000FFF,
  parameter int unsigned            DmHaltAddr       = 32'h1A110800,
  parameter int unsigned            DmExceptionAddr  = 32'h1A110808,
  parameter logic [31:0]            CsrMvendorId     = 32'b0,
  parameter logic [31:0]            CsrMimpId        = 32'b0,
  // Register file parameters
  parameter bit                     WrenCheck        = 1'b0,
  parameter bit                     RdataMuxCheck    = 1'b0,
  parameter logic [RegFileDataWidth-1:0] WordZeroVal = '0
) (
  // Clock and Reset
  input  logic                         clk_i,
  input  logic                         rst_ni,

  input  logic [31:0]                  hart_id_i,
  input  logic [31:0]                  boot_addr_i,

  // Instruction memory interface
  output logic                         instr_req_o,
  input  logic                         instr_gnt_i,
  input  logic                         instr_rvalid_i,
  output logic [31:0]                  instr_addr_o,
  input  logic [MemDataWidth-1:0]      instr_rdata_i,
  input  logic                         instr_err_i,

  // Data memory interface
  output logic                         data_req_o,
  input  logic                         data_gnt_i,
  input  logic                         data_rvalid_i,
  output logic                         data_we_o,
  output logic [3:0]                   data_be_o,
  output logic [31:0]                  data_addr_o,
  output logic [MemDataWidth-1:0]      data_wdata_o,
  input  logic [MemDataWidth-1:0]      data_rdata_i,
  input  logic                         data_err_i,

  // RAMs interface (for icache)
  output logic [IC_NUM_WAYS-1:0]       ic_tag_req_o,
  output logic                         ic_tag_write_o,
  output logic [IC_INDEX_W-1:0]        ic_tag_addr_o,
  output logic [TagSizeECC-1:0]        ic_tag_wdata_o,
  input  logic [TagSizeECC-1:0]        ic_tag_rdata_i [IC_NUM_WAYS],
  output logic [IC_NUM_WAYS-1:0]       ic_data_req_o,
  output logic                         ic_data_write_o,
  output logic [IC_INDEX_W-1:0]        ic_data_addr_o,
  output logic [LineSizeECC-1:0]       ic_data_wdata_o,
  input  logic [LineSizeECC-1:0]       ic_data_rdata_i [IC_NUM_WAYS],
  input  logic                         ic_scr_key_valid_i,
  output logic                         ic_scr_key_req_o,

  // Interrupt inputs
  input  logic                         irq_software_i,
  input  logic                         irq_timer_i,
  input  logic                         irq_external_i,
  input  logic [14:0]                  irq_fast_i,
  input  logic                         irq_nm_i,

  // Debug interface
  input  logic                         debug_req_i,
  output crash_dump_t                  crash_dump_o,
  output logic                         double_fault_seen_o,

  // CPU control signals
  input  ibex_mubi_t                   fetch_enable_i,
  output logic                         alert_minor_o,
  output logic                         alert_major_internal_o,
  output logic                         alert_major_bus_o,
  output logic                         core_busy_o
);

  // Register file interface signals
  logic                         dummy_instr_id;
  logic                         dummy_instr_wb;
  logic [4:0]                   rf_raddr_a;
  logic [4:0]                   rf_raddr_b;
  logic [4:0]                   rf_waddr_wb;
  logic                         rf_we_wb;
  logic [RegFileDataWidth-1:0]  rf_wdata_wb;
  logic [RegFileDataWidth-1:0]  rf_rdata_a;
  logic [RegFileDataWidth-1:0]  rf_rdata_b;
  logic                         rf_err;

  // Instantiate ibex_core
  ibex_core #(
    .PMPEnable        (PMPEnable),
    .PMPGranularity   (PMPGranularity),
    .PMPNumRegions    (PMPNumRegions),
    .PMPRstCfg        (PMPRstCfg),
    .PMPRstAddr       (PMPRstAddr),
    .PMPRstMsecCfg    (PMPRstMsecCfg),
    .MHPMCounterNum   (MHPMCounterNum),
    .MHPMCounterWidth (MHPMCounterWidth),
    .RV32E            (RV32E),
    .RV32M            (RV32M),
    .RV32B            (RV32B),
    .BranchTargetALU  (BranchTargetALU),
    .WritebackStage   (WritebackStage),
    .ICache           (ICache),
    .ICacheECC        (ICacheECC),
    .BusSizeECC       (BusSizeECC),
    .TagSizeECC       (TagSizeECC),
    .LineSizeECC      (LineSizeECC),
    .BranchPredictor  (BranchPredictor),
    .DbgTriggerEn     (DbgTriggerEn),
    .DbgHwBreakNum    (DbgHwBreakNum),
    .ResetAll         (ResetAll),
    .RndCnstLfsrSeed  (RndCnstLfsrSeed),
    .RndCnstLfsrPerm  (RndCnstLfsrPerm),
    .SecureIbex       (SecureIbex),
    .DummyInstructions(DummyInstructions),
    .RegFileECC       (RegFileECC),
    .RegFileDataWidth (RegFileDataWidth),
    .MemECC           (MemECC),
    .MemDataWidth     (MemDataWidth),
    .DmBaseAddr       (DmBaseAddr),
    .DmAddrMask       (DmAddrMask),
    .DmHaltAddr       (DmHaltAddr),
    .DmExceptionAddr  (DmExceptionAddr),
    .CsrMvendorId     (CsrMvendorId),
    .CsrMimpId        (CsrMimpId)
  ) core_i (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .hart_id_i           (hart_id_i),
    .boot_addr_i         (boot_addr_i),

    // Instruction memory
    .instr_req_o         (instr_req_o),
    .instr_gnt_i         (instr_gnt_i),
    .instr_rvalid_i      (instr_rvalid_i),
    .instr_addr_o        (instr_addr_o),
    .instr_rdata_i       (instr_rdata_i),
    .instr_err_i         (instr_err_i),

    // Data memory
    .data_req_o          (data_req_o),
    .data_gnt_i          (data_gnt_i),
    .data_rvalid_i       (data_rvalid_i),
    .data_we_o           (data_we_o),
    .data_be_o           (data_be_o),
    .data_addr_o         (data_addr_o),
    .data_wdata_o        (data_wdata_o),
    .data_rdata_i        (data_rdata_i),
    .data_err_i          (data_err_i),

    // Register file interface
    .dummy_instr_id_o    (dummy_instr_id),
    .dummy_instr_wb_o    (dummy_instr_wb),
    .rf_raddr_a_o        (rf_raddr_a),
    .rf_raddr_b_o        (rf_raddr_b),
    .rf_waddr_wb_o       (rf_waddr_wb),
    .rf_we_wb_o          (rf_we_wb),
    .rf_wdata_wb_ecc_o   (rf_wdata_wb),
    .rf_rdata_a_ecc_i    (rf_rdata_a),
    .rf_rdata_b_ecc_i    (rf_rdata_b),

    // ICache RAM interface
    .ic_tag_req_o        (ic_tag_req_o),
    .ic_tag_write_o      (ic_tag_write_o),
    .ic_tag_addr_o       (ic_tag_addr_o),
    .ic_tag_wdata_o      (ic_tag_wdata_o),
    .ic_tag_rdata_i      (ic_tag_rdata_i),
    .ic_data_req_o       (ic_data_req_o),
    .ic_data_write_o     (ic_data_write_o),
    .ic_data_addr_o      (ic_data_addr_o),
    .ic_data_wdata_o     (ic_data_wdata_o),
    .ic_data_rdata_i     (ic_data_rdata_i),
    .ic_scr_key_valid_i  (ic_scr_key_valid_i),
    .ic_scr_key_req_o    (ic_scr_key_req_o),

    // Interrupts
    .irq_software_i      (irq_software_i),
    .irq_timer_i         (irq_timer_i),
    .irq_external_i      (irq_external_i),
    .irq_fast_i          (irq_fast_i),
    .irq_nm_i            (irq_nm_i),

    // Debug
    .debug_req_i         (debug_req_i),
    .crash_dump_o        (crash_dump_o),
    .double_fault_seen_o (double_fault_seen_o),

    // CPU Control
    .fetch_enable_i      (fetch_enable_i),
    .alert_minor_o       (alert_minor_o),
    .alert_major_internal_o(alert_major_internal_o),
    .alert_major_bus_o   (alert_major_bus_o),
    .core_busy_o         (core_busy_o)
  );

  // Instantiate register file
  ibex_register_file_ff #(
    .RV32E            (RV32E),
    .DataWidth        (RegFileDataWidth),
    .DummyInstructions(DummyInstructions),
    .WrenCheck        (WrenCheck),
    .RdataMuxCheck    (RdataMuxCheck),
    .WordZeroVal      (WordZeroVal)
  ) register_file_i (
    .clk_i            (clk_i),
    .rst_ni           (rst_ni),
    .test_en_i        (1'b0),  // Tie off test enable
    .dummy_instr_id_i (dummy_instr_id),
    .dummy_instr_wb_i (dummy_instr_wb),
    .raddr_a_i        (rf_raddr_a),
    .rdata_a_o        (rf_rdata_a),
    .raddr_b_i        (rf_raddr_b),
    .rdata_b_o        (rf_rdata_b),
    .waddr_a_i        (rf_waddr_wb),
    .wdata_a_i        (rf_wdata_wb),
    .we_a_i           (rf_we_wb),
    .err_o            (rf_err)
  );

endmodule
