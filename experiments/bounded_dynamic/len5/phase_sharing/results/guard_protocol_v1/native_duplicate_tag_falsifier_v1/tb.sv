module tb;
reg [0:0] clk_i;
reg [0:0] rst_ni;
reg [0:0] flush_i;
reg [0:0] issue_valid_i;
reg [3:0] issue_eu_ctl_i;
reg [69:0] issue_rs1_i;
reg [69:0] issue_rs2_i;
reg [4:0] issue_dest_rob_idx_i;
reg [0:0] max_prio_valid_i;
reg [74:0] max_prio_data_i;
reg [4:0] other_valid_i;
reg [374:0] other_data_i;
reg [0:0] rob_ready_i;
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

reg [31:0] prng=32'h13579bdf;
integer cycle;
reg [4:0] tag1,tag2,tagd;
reg [63:0] val1,val2;
reg r1,r2;
task step;
begin
 clk_i=0; #4;
 if ({ref_issue_ready_o,ref_max_prio_ready_o,ref_cdb_ready_o,ref_cdb_valid_o,ref_observed_cdb_o} !==
     {cand_issue_ready_o,cand_max_prio_ready_o,cand_cdb_ready_o,cand_cdb_valid_o,cand_observed_cdb_o}) begin
 $display("MISMATCH cycle=%0d ref_valid=%b cand_valid=%b ref_data=%h cand_data=%h",cycle,ref_cdb_valid_o,cand_cdb_valid_o,ref_observed_cdb_o,cand_observed_cdb_o);
 $finish;
 end
 $display("TRACE cycle=%0d rst=%b flush=%b valid=%b ready=%b rs1=%h rs2=%h dest=%d maxvalid=%b maxdata=%h robready=%b outvalid=%b out=%h",cycle,rst_ni,flush_i,issue_valid_i,ref_issue_ready_o,issue_rs1_i,issue_rs2_i,issue_dest_rob_idx_i,max_prio_valid_i,max_prio_data_i,rob_ready_i,ref_cdb_valid_o,ref_observed_cdb_o);
 clk_i=1;#4;
end
endtask
initial begin
 clk_i=0;rst_ni=0;flush_i=0;issue_valid_i=0;issue_eu_ctl_i=0;issue_rs1_i=0;issue_rs2_i=0;issue_dest_rob_idx_i=0;max_prio_valid_i=0;max_prio_data_i=0;other_valid_i=0;other_data_i=0;rob_ready_i=0;cycle=0;
 step;rst_ni=1;
 for(cycle=1;cycle<=8;cycle=cycle+1) begin
 issue_valid_i=1;issue_rs1_i={1'b0,5'd5,64'd100};issue_rs2_i={1'b0,5'd5,64'd200};issue_dest_rob_idx_i=0;step;
 end
 issue_valid_i=0;max_prio_valid_i=1;max_prio_data_i={5'd5,64'd7,6'd0};step;cycle=cycle+1;
 max_prio_valid_i=0;
 for(;cycle<100000;cycle=cycle+1) begin
 prng=prng^(prng<<13);prng=prng^(prng>>17);prng=prng^(prng<<5);
 issue_valid_i=prng[0]|prng[1];r1=prng[2];r2=prng[3];
 tag1={3'd0,prng[5:4]};tag2={3'd0,prng[7:6]};tagd={3'd0,prng[9:8]};
 val1={prng,~prng};val2={~prng,prng};
 issue_rs1_i={r1,tag1,val1};issue_rs2_i={r2,tag2,val2};issue_dest_rob_idx_i=tagd;
 rob_ready_i=(cycle%31)>15;
 max_prio_valid_i=prng[10]&prng[11]&prng[12];max_prio_data_i={tag1,val2,6'd0};
 flush_i=(cycle%503)==0;
 step;
 end
 $display("NO_MISMATCH cycles=%0d",cycle);$finish;
end
endmodule
