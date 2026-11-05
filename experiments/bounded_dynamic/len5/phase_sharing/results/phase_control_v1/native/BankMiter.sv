// Shared external inputs; only an initial reset is assumed.
module BankMiter(
  input wire [0:0] clk_i,
  input wire [0:0] rst_ni,
  input wire [0:0] flush_i,
  input wire [0:0] issue_valid_i,
  input wire [3:0] issue_eu_ctl_i,
  input wire [69:0] issue_rs1_i,
  input wire [69:0] issue_rs2_i,
  input wire [4:0] issue_dest_rob_idx_i,
  input wire [0:0] max_prio_valid_i,
  input wire [74:0] max_prio_data_i,
  input wire [4:0] other_valid_i,
  input wire [374:0] other_data_i,
  input wire [0:0] rob_ready_i
);
  always @* if ($initstate) assume (!rst_ni);
  wire [0:0] ref_issue_ready_o, cand_issue_ready_o;
  wire [0:0] ref_max_prio_ready_o, cand_max_prio_ready_o;
  wire [4:0] ref_cdb_ready_o, cand_cdb_ready_o;
  wire [0:0] ref_cdb_valid_o, cand_cdb_valid_o;
  wire [74:0] ref_observed_cdb_o, cand_observed_cdb_o;
  AluReference reference(
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .flush_i(flush_i),
    .issue_valid_i(issue_valid_i),
    .issue_eu_ctl_i(issue_eu_ctl_i),
    .issue_rs1_i(issue_rs1_i),
    .issue_rs2_i(issue_rs2_i),
    .issue_dest_rob_idx_i(issue_dest_rob_idx_i),
    .max_prio_valid_i(max_prio_valid_i),
    .max_prio_data_i(max_prio_data_i),
    .other_valid_i(other_valid_i),
    .other_data_i(other_data_i),
    .rob_ready_i(rob_ready_i),
    .issue_ready_o(ref_issue_ready_o),
    .max_prio_ready_o(ref_max_prio_ready_o),
    .cdb_ready_o(ref_cdb_ready_o),
    .cdb_valid_o(ref_cdb_valid_o),
    .observed_cdb_o(ref_observed_cdb_o)
  );
  AluCandidate candidate(
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .flush_i(flush_i),
    .issue_valid_i(issue_valid_i),
    .issue_eu_ctl_i(issue_eu_ctl_i),
    .issue_rs1_i(issue_rs1_i),
    .issue_rs2_i(issue_rs2_i),
    .issue_dest_rob_idx_i(issue_dest_rob_idx_i),
    .max_prio_valid_i(max_prio_valid_i),
    .max_prio_data_i(max_prio_data_i),
    .other_valid_i(other_valid_i),
    .other_data_i(other_data_i),
    .rob_ready_i(rob_ready_i),
    .issue_ready_o(cand_issue_ready_o),
    .max_prio_ready_o(cand_max_prio_ready_o),
    .cdb_ready_o(cand_cdb_ready_o),
    .cdb_valid_o(cand_cdb_valid_o),
    .observed_cdb_o(cand_observed_cdb_o)
  );
  always @* assert (ref_issue_ready_o == cand_issue_ready_o);
  always @* assert (ref_max_prio_ready_o == cand_max_prio_ready_o);
  always @* assert (ref_cdb_ready_o == cand_cdb_ready_o);
  always @* assert (ref_cdb_valid_o == cand_cdb_valid_o);
  always @* assert (ref_observed_cdb_o == cand_observed_cdb_o);
endmodule
