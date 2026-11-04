// Read-only simulation observer. No core state, output, or handshake is driven.
// Included in the generated upstream tb_bare module, never in synthesized RTL.
`define QROB u_datapath.u_backend.u_commit_stage.u_rob
`define QALU u_datapath.u_backend.u_exec_stage.u_alu_unit.u_arith_rs
`define QLB u_datapath.u_backend.u_exec_stage.u_load_store_unit.u_load_buffer
integer qualification_fd;
initial begin
  qualification_fd = $fopen("logs/qualification_events.csv", "w");
  $fdisplay(qualification_fd, "cycle,event,rob,v0,v1");
end
always @(posedge clk_i) begin
  if (!rst_ni) begin
    $fdisplay(qualification_fd, "%0d,RESET,0,0,0", curr_cycle);
  end else if (`QROB.flush_i) begin
    $fdisplay(qualification_fd, "%0d,FLUSH,0,0,0", curr_cycle);
  end else begin
    if (`QROB.fifo_push)
      $fdisplay(qualification_fd, "%0d,DISPATCH,%0d,%h,%h", curr_cycle,
                `QROB.tail_idx, `QROB.issue_data_i.instr_pc, `QROB.issue_data_i.instruction.raw);
    if (`QALU.ex_accepted)
      $fdisplay(qualification_fd, "%0d,ALU_START,%0d,0,0", curr_cycle, `QALU.eu_rob_idx_o);
    if (`QALU.save_res)
      $fdisplay(qualification_fd, "%0d,ALU_RESULT,%0d,%h,0", curr_cycle,
                `QALU.eu_rob_idx_i, `QALU.eu_result_i);
    if (`QLB.mem_accepted)
      $fdisplay(qualification_fd, "%0d,LOAD_REQUEST,%0d,%h,%h", curr_cycle,
                `QLB.data[`QLB.mem_idx].dest_rob_idx, `QLB.mem_idx, `QLB.mem_addr_o);
    if (`QLB.save_mem)
      $fdisplay(qualification_fd, "%0d,LOAD_RESPONSE,0,%h,%h", curr_cycle,
                `QLB.mem_tag_i, `QLB.mem_rdata_i);
  end
end
final $fclose(qualification_fd);
`undef QROB
`undef QALU
`undef QLB
