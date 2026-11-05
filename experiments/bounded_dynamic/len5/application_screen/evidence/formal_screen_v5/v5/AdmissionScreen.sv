module AdmissionScreen(input wire clk_i, rst_ni,
  input wire [3:0] instruction_choice, input wire [63:0] load_value,
  input wire [2:0] invalid_code_nonzero);
  always @* if ($initstate) assume (!rst_ni);
  wire [0:0] mem_flush_o;
  wire [0:0] instr_req_o;
  wire [0:0] instr_gnt_i;
  wire [0:0] instr_rvalid_i;
  wire [0:0] instr_rready_o;
  wire [0:0] instr_we_o;
  wire [63:0] instr_addr_o;
  wire [31:0] instr_rdata_i;
  wire [0:0] instr_except_raised_i;
  wire [4:0] instr_except_code_i;
  wire [0:0] data_load_req_o;
  wire [0:0] data_load_gnt_i;
  wire [0:0] data_load_rvalid_i;
  wire [0:0] data_load_rready_o;
  wire [0:0] data_load_we_o;
  wire [63:0] data_load_addr_o;
  wire [3:0] data_load_tag_o;
  wire [7:0] data_load_be_o;
  wire [63:0] data_load_rdata_i;
  wire [3:0] data_load_tag_i;
  wire [0:0] data_load_except_raised_i;
  wire [4:0] data_load_except_code_i;
  wire [0:0] data_store_req_o;
  wire [0:0] data_store_gnt_i;
  wire [0:0] data_store_rvalid_i;
  wire [0:0] data_store_rready_o;
  wire [0:0] data_store_we_o;
  wire [63:0] data_store_addr_o;
  wire [3:0] data_store_tag_o;
  wire [7:0] data_store_be_o;
  wire [63:0] data_store_wdata_o;
  wire [3:0] data_store_tag_i;
  wire [0:0] data_store_except_raised_i;
  wire [4:0] data_store_except_code_i;
  wire [31:0] irq_i;
  wire [0:0] irq_ack_o;
  wire [4:0] irq_id_o;
  wire [0:0] fetch_enable_i;
  wire [0:0] core_sleep_o;
  wire [0:0] probe_insert;
  wire [2:0] probe_index;
  ObservedCore dut(.clk_i(clk_i),.rst_ni(rst_ni),.mem_flush_o(mem_flush_o),.instr_req_o(instr_req_o),.instr_gnt_i(instr_gnt_i),.instr_rvalid_i(instr_rvalid_i),.instr_rready_o(instr_rready_o),.instr_we_o(instr_we_o),.instr_addr_o(instr_addr_o),.instr_rdata_i(instr_rdata_i),.instr_except_raised_i(instr_except_raised_i),.instr_except_code_i(instr_except_code_i),.data_load_req_o(data_load_req_o),.data_load_gnt_i(data_load_gnt_i),.data_load_rvalid_i(data_load_rvalid_i),.data_load_rready_o(data_load_rready_o),.data_load_we_o(data_load_we_o),.data_load_addr_o(data_load_addr_o),.data_load_tag_o(data_load_tag_o),.data_load_be_o(data_load_be_o),.data_load_rdata_i(data_load_rdata_i),.data_load_tag_i(data_load_tag_i),.data_load_except_raised_i(data_load_except_raised_i),.data_load_except_code_i(data_load_except_code_i),.data_store_req_o(data_store_req_o),.data_store_gnt_i(data_store_gnt_i),.data_store_rvalid_i(data_store_rvalid_i),.data_store_rready_o(data_store_rready_o),.data_store_we_o(data_store_we_o),.data_store_addr_o(data_store_addr_o),.data_store_tag_o(data_store_tag_o),.data_store_be_o(data_store_be_o),.data_store_wdata_o(data_store_wdata_o),.data_store_tag_i(data_store_tag_i),.data_store_except_raised_i(data_store_except_raised_i),.data_store_except_code_i(data_store_except_code_i),.irq_i(irq_i),.irq_ack_o(irq_ack_o),.irq_id_o(irq_id_o),.fetch_enable_i(fetch_enable_i),.core_sleep_o(core_sleep_o),.probe_insert(probe_insert),.probe_index(probe_index));
  reg [31:0] selected_instruction;
  always @* begin
    selected_instruction = 32'h00000013;
    case (instruction_choice)
      4'd0: selected_instruction = 32'h00001437;
      4'd1: selected_instruction = 32'h000024b7;
      4'd2: selected_instruction = 32'h04000913;
      4'd3: selected_instruction = 32'h00043503;
      4'd4: selected_instruction = 32'h00150593;
      4'd5: selected_instruction = 32'h00b4b023;
      4'd6: selected_instruction = 32'h00840413;
      4'd7: selected_instruction = 32'h00848493;
      4'd8: selected_instruction = 32'hfff90913;
      4'd9: selected_instruction = 32'hfe0914e3;
      4'd10: selected_instruction = 32'h200002b7;
      4'd11: selected_instruction = 32'h1002829b;
      4'd12: selected_instruction = 32'h00028023;
      4'd13: selected_instruction = 32'h0000006f;
      default: ;
    endcase
  end
  assign irq_i = 0;
  assign fetch_enable_i = 1;
  assign instr_except_raised_i = 0;
  assign instr_except_code_i = (instr_rvalid_i || invalid_code_nonzero[0]) ? 31 : 0;
  assign data_load_except_raised_i = 0;
  assign data_load_except_code_i = (data_load_rvalid_i || invalid_code_nonzero[1]) ? 31 : 0;
  assign data_store_except_raised_i = 0;
  assign data_store_except_code_i = (data_store_rvalid_i || invalid_code_nonzero[2]) ? 31 : 0;
  // Native two-stage fetch pipeline: freeze with core response readiness.
  // SKIP_INS_ANS_REG=1 couples upstream grant to this same readiness.
  reg [1:0] iv; reg [31:0] ins0, ins1;
  reg [0:0] gap_left;
  wire gate_open = gap_left == 0;
  wire ipush = instr_req_o && instr_gnt_i;
  assign instr_gnt_i = instr_rready_o && gate_open;
  assign instr_rvalid_i = iv[1];
  assign instr_rdata_i = ins1;
  always @(posedge clk_i) begin
    if (!rst_ni) begin
      iv <= 0; ins0 <= 0; ins1 <= 0; gap_left <= 0;
    end else begin
      if (gap_left != 0) gap_left <= gap_left - 1;
      if (ipush) gap_left <= 1;
      if (mem_flush_o) begin iv <= 0; ins0 <= 0; ins1 <= 0; end
      else if (instr_rready_o) begin
        iv <= {iv[0], instr_req_o && gate_open};
        ins0 <= (instr_req_o && gate_open) ? selected_instruction : 0;
        ins1 <= ins0;
      end
    end
  end
  // A fully pipelined data service; flush never cancels data replies.
  reg [2:0] lv, sv;
  reg [3:0] lt0, lt1, lt2, st0, st1, st2;
  reg [63:0] ld0, ld1, ld2;
  assign data_load_gnt_i = rst_ni; assign data_store_gnt_i = rst_ni;
  assign data_load_rvalid_i = lv[2]; assign data_store_rvalid_i = sv[2];
  assign data_load_tag_i = lt2; assign data_store_tag_i = st2;
  assign data_load_rdata_i = ld2;
  always @(posedge clk_i) begin
    if (!rst_ni) begin
      lv <= 0; sv <= 0; lt0 <= 0; lt1 <= 0; lt2 <= 0;
      st0 <= 0; st1 <= 0; st2 <= 0; ld0 <= 0; ld1 <= 0; ld2 <= 0;
    end else begin
      lv <= {lv[1:0], data_load_req_o}; sv <= {sv[1:0], data_store_req_o};
      lt0 <= data_load_tag_o; lt1 <= lt0; lt2 <= lt1;
      st0 <= data_store_tag_o; st1 <= st0; st2 <= st1;
      ld0 <= load_value; ld1 <= ld0; ld2 <= ld1;
    end
  end
  // These are proof obligations, never premises on internal service.
  always @* if (rst_ni) begin
    assert (!data_load_rvalid_i || data_load_rready_o);
    assert (!data_store_rvalid_i || data_store_rready_o);
    assert (!(probe_insert && probe_index < 3'd4));
  end
endmodule
