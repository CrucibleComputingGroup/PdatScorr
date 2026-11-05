// A component experiment boundary, not replacement LEN5 RTL.
// Native ALU8, native six-producer CDB arbitration, native ROB32.
// Other producers/dispatch/commit are arbitrary external inputs.
module AluObserved #(
  parameter bit RAW_CDB = 1'b0
) (
  input logic clk_i, rst_ni, flush_i,
  input logic issue_valid_i,
  input expipe_pkg::alu_ctl_t issue_eu_ctl_i,
  input expipe_pkg::op_data_t issue_rs1_i, issue_rs2_i,
  input expipe_pkg::rob_idx_t issue_dest_rob_idx_i,
  output logic issue_ready_o,
  input logic max_prio_valid_i,
  input expipe_pkg::cdb_data_t max_prio_data_i,
  input logic [len5_config_pkg::MAX_EU_N-2:0] other_valid_i,
  input expipe_pkg::cdb_data_t [len5_config_pkg::MAX_EU_N-2:0] other_data_i,
  output logic max_prio_ready_o,
  output logic [len5_config_pkg::MAX_EU_N-2:0] cdb_ready_o,
  output logic cdb_valid_o,
  output expipe_pkg::cdb_data_t observed_cdb_o,
  input logic rob_issue_valid_i,
  input expipe_pkg::rob_entry_t rob_issue_data_i,
  input expipe_pkg::rob_idx_t rob_rs1_idx_i, rob_rs2_idx_i, sb_mem_idx_i,
  input logic comm_ready_i,
  output logic rob_issue_ready_o,
  output expipe_pkg::rob_idx_t rob_issue_tail_idx_o,
  output logic opfwd_rs1_valid_o, opfwd_rs1_ready_o,
  output logic [len5_pkg::XLEN-1:0] opfwd_rs1_value_o,
  output logic opfwd_rs2_valid_o, opfwd_rs2_ready_o,
  output logic [len5_pkg::XLEN-1:0] opfwd_rs2_value_o,
  output logic sb_mem_clear_o, comm_valid_o,
  output expipe_pkg::rob_entry_t comm_data_o,
  output expipe_pkg::rob_idx_t comm_idx_o
);
  import len5_config_pkg::*;
  import expipe_pkg::*;
  localparam int ALU_SLOT = int'(EU_INT_ALU) - 1;
  logic [MAX_EU_N-2:0] producer_valid;
  cdb_data_t [MAX_EU_N-2:0] producer_data;
  logic alu_valid, rob_cdb_ready;
  cdb_data_t alu_data, cdb_data;
  always_comb begin
    producer_valid = other_valid_i;
    producer_data = other_data_i;
    producer_valid[ALU_SLOT] = alu_valid;
    producer_data[ALU_SLOT] = alu_data;
  end
  alu_unit #(.RS_DEPTH(ALU_RS_DEPTH), .EU_CTL_LEN($bits(alu_ctl_t)),
             .RR_ARBITER(ALU_RR_ARBITER)) u_alu (
    .clk_i, .rst_ni, .flush_i, .issue_valid_i, .issue_ready_o,
    .issue_eu_ctl_i, .issue_rs1_i, .issue_rs2_i, .issue_dest_rob_idx_i,
    .cdb_ready_i(cdb_ready_o[ALU_SLOT]), .cdb_valid_i(cdb_valid_o),
    .cdb_data_i(cdb_data), .cdb_valid_o(alu_valid), .cdb_data_o(alu_data)
  );
  cdb u_cdb (
    .clk_i, .rst_ni, .flush_i,
    .max_prio_valid_i, .max_prio_ready_o, .max_prio_data_i,
    .rs_valid_i(producer_valid), .rs_ready_o(cdb_ready_o),
    .rs_data_i(producer_data), .rob_ready_i(rob_cdb_ready),
    .valid_o(cdb_valid_o), .data_o(cdb_data)
  );
  // The raw variant is a falsifier, not a changed acceptance criterion.
  assign observed_cdb_o = (RAW_CDB || cdb_valid_o) ? cdb_data : '0;
  rob #(.DEPTH(ROB_DEPTH)) u_rob (
    .clk_i, .rst_ni, .flush_i,
    .issue_valid_i(rob_issue_valid_i), .issue_ready_o(rob_issue_ready_o),
    .issue_data_i(rob_issue_data_i), .issue_tail_idx_o(rob_issue_tail_idx_o),
    .issue_rs1_rob_idx_i(rob_rs1_idx_i), .issue_rs2_rob_idx_i(rob_rs2_idx_i),
    .opfwd_rs1_valid_o, .opfwd_rs1_ready_o, .opfwd_rs1_value_o,
    .opfwd_rs2_valid_o, .opfwd_rs2_ready_o, .opfwd_rs2_value_o,
    .sb_mem_idx_i, .sb_mem_clear_o, .comm_valid_o, .comm_ready_i,
    .comm_data_o, .comm_idx_o, .cdb_valid_i(cdb_valid_o),
    .cdb_data_i(cdb_data), .cdb_ready_o(rob_cdb_ready)
  );
endmodule
