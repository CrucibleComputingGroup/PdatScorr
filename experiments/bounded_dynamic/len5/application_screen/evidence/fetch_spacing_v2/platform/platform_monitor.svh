// Read-only edge observer for actual external handshakes and flushes.
integer platform_fd;
initial begin
  platform_fd = $fopen("logs/platform_edges.csv", "w");
  $fdisplay(platform_fd, "cycle,reset_n,flush,core_req,core_gnt,memory_req,memory_gnt,fetch_addr,fetch_response_valid,fetch_response_ready,load_req,load_gnt,load_addr,load_tag,load_response_valid,load_response_ready,load_response_tag");
end
always @(posedge clk_i) begin
  $fdisplay(platform_fd, "%0d,%0d,%0d,%0d,%0d,%0d,%0d,%h,%0d,%0d,%0d,%0d,%h,%h,%0d,%0d,%h",
    curr_cycle, rst_ni, dp2mem_flush,
    u_datapath.instr_req_o, u_datapath.instr_gnt_i,
    u_memory_bare_emu.instr_valid_i, u_memory_bare_emu.instr_ready_o,
    dp2mem_instr_addr, mem2dp_instr_valid, dp2mem_instr_ready,
    dp2mem_load_valid, mem2dp_load_ready, dp2mem_load_addr, dp2mem_load_tag,
    mem2dp_load_valid, dp2mem_load_ready, mem2dp_load_tag);
end
final $fclose(platform_fd);
