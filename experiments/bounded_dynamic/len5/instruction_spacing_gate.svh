// External testbench platform only. No core RTL or capacity is changed.
// InstrMinAcceptSpacing is supplied by the simulation builder.
logic qualification_instr_memory_ready;
logic qualification_instr_memory_valid;
logic qualification_instr_gate_open;
integer unsigned qualification_instr_cooldown;

assign qualification_instr_gate_open = qualification_instr_cooldown == 0;
assign qualification_instr_memory_valid = dp2mem_instr_valid && qualification_instr_gate_open;
assign mem2dp_instr_ready = qualification_instr_memory_ready && qualification_instr_gate_open;

// Throttle accepted requests, not the response pipeline. A flush still reaches
// the original memory model directly and does not reset external port bandwidth.
always_ff @(posedge clk_i or negedge rst_ni) begin
  if (!rst_ni) qualification_instr_cooldown <= 0;
  else if (dp2mem_instr_valid && mem2dp_instr_ready)
    qualification_instr_cooldown <= InstrMinAcceptSpacing - 1;
  else if (qualification_instr_cooldown != 0)
    qualification_instr_cooldown <= qualification_instr_cooldown - 1;
end

always @(posedge clk_i) begin
  if (rst_ni) begin
    assert ((u_datapath.instr_req_o && u_datapath.instr_gnt_i) ==
            (u_memory_bare_emu.instr_valid_i && u_memory_bare_emu.instr_ready_o))
      else $fatal(1, "Instruction gate handshake mismatch");
  end
end
