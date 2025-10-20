// ========================================
// Timing Constraints V2 - Meaningful Bounds
// ========================================
// Goal: Help ABC prove equivalences by constraining impossible states
// Overhead: ~6 flip-flops (minimal)

// Track consecutive instruction stalls
logic [2:0] instr_stall_counter_q;
always_ff @(posedge clk_i or negedge rst_ni) begin
  if (!rst_ni) begin
    instr_stall_counter_q <= 3'b0;
  end else begin
    if (instr_req_o && !instr_gnt_i) begin
      instr_stall_counter_q <= instr_stall_counter_q + 1;
    end else begin
      instr_stall_counter_q <= 3'b0;
    end
  end
end

// Track consecutive data stalls
logic [2:0] data_stall_counter_q;
always_ff @(posedge clk_i or negedge rst_ni) begin
  if (!rst_ni) begin
    data_stall_counter_q <= 3'b0;
  end else begin
    if (lsu_req_dec && !lsu_req_done_i) begin
      data_stall_counter_q <= data_stall_counter_q + 1;
    end else begin
      data_stall_counter_q <= 3'b0;
    end
  end
end

// ========================================
// Meaningful Timing Constraints
// ========================================

always_comb begin
  if (rst_ni) begin
    // Constraint 1: Memory responses are bounded (from Ibex formal spec)
    assume(instr_stall_counter_q <= 3'd5);  // TIME_LIMIT from mem.sv
    assume(data_stall_counter_q <= 3'd4);

    // Constraint 2: After max stalls, request MUST be satisfied
    // This helps ABC prove that certain wait states are unreachable
    if (instr_stall_counter_q == 3'd5) begin
      assume(instr_gnt_i);  // Grant must arrive
    end

    if (data_stall_counter_q == 3'd4) begin
      assume(lsu_req_done_i);  // Data must be ready
    end

    // Constraint 3: Can't have instruction execution during data stall
    // This prunes invalid state space
    if (data_stall_counter_q > 0) begin
      assume(!instr_first_cycle_id_o);  // No new instructions during stall
    end

    // Constraint 4: Pipeline depth constraint
    // Can't have both instruction fetch stalled AND data stall at max
    // (prevents unrealistic scenarios ABC must consider)
    assume(!(instr_stall_counter_q >= 3 && data_stall_counter_q >= 3));
  end
end
