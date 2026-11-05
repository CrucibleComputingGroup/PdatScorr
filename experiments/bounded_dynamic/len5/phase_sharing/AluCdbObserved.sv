// Original ALU8 + six-producer CDB. Downstream consumer closure is proved
// separately on all actual LEN5 core outputs and next-state bits.
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
  input logic rob_ready_i,
  output logic max_prio_ready_o,
  output logic [len5_config_pkg::MAX_EU_N-2:0] cdb_ready_o,
  output logic cdb_valid_o,
  output expipe_pkg::cdb_data_t observed_cdb_o
);
  import len5_config_pkg::*;
  import expipe_pkg::*;
  localparam int ALU_SLOT = int'(EU_INT_ALU) - 1;
  logic [MAX_EU_N-2:0] producer_valid;
  cdb_data_t [MAX_EU_N-2:0] producer_data;
  logic alu_valid;
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
    .rs_data_i(producer_data), .rob_ready_i,
    .valid_o(cdb_valid_o), .data_o(cdb_data)
  );
  assign observed_cdb_o = (RAW_CDB || cdb_valid_o) ? cdb_data : '0;
endmodule
