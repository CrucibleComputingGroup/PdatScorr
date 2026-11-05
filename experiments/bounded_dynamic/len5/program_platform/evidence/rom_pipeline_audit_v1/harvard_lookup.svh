// Explicit external Harvard platform; this file never changes core RTL.
// Only instruction lookup differs from upstream memory_bare_emu. All pipeline,
// readiness, flush, load/store, and memory-write logic remains upstream.
memory_class instruction_mem;
string instruction_rom_path;
initial begin
  if (!$value$plusargs("instruction_rom=%s", instruction_rom_path))
    $fatal(1, "Harvard platform requires +instruction_rom=<ELF executable image>");
  instruction_mem = new(instruction_rom_path);
  if (instruction_mem.LoadMem() <= 0)
    $fatal(1, "Unable to load instruction ROM image");
end

function automatic instr_mem_ans_t lookup_instruction_rom(input logic [XLEN-1:0] address);
  instr_mem_ans_t answer;
  bit mapped;
  answer = '0;
  answer.except_code = E_UNKNOWN;
  mapped = 1'b1;
  if (address[1:0] != 2'b00) begin
    answer.except_raised = 1'b1;
    answer.except_code = E_I_ADDR_MISALIGNED;
  end else begin
    for (int byte_index = 0; byte_index < 4; byte_index++)
      if (!instruction_mem.mem.exists(address + XLEN'(byte_index))) mapped = 1'b0;
    if (!mapped) begin
      answer.except_raised = 1'b1;
      answer.except_code = E_I_ACCESS_FAULT;
    end else begin
      for (int byte_index = 0; byte_index < 4; byte_index++)
        answer.read[8*byte_index +: 8] = instruction_mem.mem[address + XLEN'(byte_index)];
    end
  end
  return answer;
endfunction

always_comb begin : p_ins_mem_req
  instr_pipe_reg[0] = '0;
  instr_pipe_reg[0].except_code = E_UNKNOWN;
  if (instr_valid_i) instr_pipe_reg[0] = lookup_instruction_rom(instr_addr_i);
end
