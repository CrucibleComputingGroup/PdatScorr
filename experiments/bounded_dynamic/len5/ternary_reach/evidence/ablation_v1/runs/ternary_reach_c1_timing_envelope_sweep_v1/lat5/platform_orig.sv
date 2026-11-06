module Platform_orig(input wire clk_i, rst_ni,
  input wire [3:0] instruction_choice, input wire [63:0] load_value,
  input wire [2:0] invalid_code_nonzero, input wire [31:0] instruction_fault_data,
  input wire fetch_gate, load_gnt, store_gnt, input wire [7:0] load_lat, store_lat,
  output wire [24156:0] obs_ffq, output wire obs_insert, output wire [2:0] obs_index,
  output wire obs_fetch, output wire [63:0] obs_fetch_addr, output wire obs_store,
  output wire [63:0] obs_store_addr, output wire obs_load, output wire obs_flush,
  output wire [296:0] obs_core, output wire [63:0] obs_load_addr, output wire [63:0] obs_store_data,
  output wire [7:0] obs_store_be, output wire obs_service_ok);
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
  wire [24156:0] ffq_obs;
  Core_orig dut(.clk_i(clk_i),.rst_ni(rst_ni),.mem_flush_o(mem_flush_o),.instr_req_o(instr_req_o),.instr_gnt_i(instr_gnt_i),.instr_rvalid_i(instr_rvalid_i),.instr_rready_o(instr_rready_o),.instr_we_o(instr_we_o),.instr_addr_o(instr_addr_o),.instr_rdata_i(instr_rdata_i),.instr_except_raised_i(instr_except_raised_i),.instr_except_code_i(instr_except_code_i),.data_load_req_o(data_load_req_o),.data_load_gnt_i(data_load_gnt_i),.data_load_rvalid_i(data_load_rvalid_i),.data_load_rready_o(data_load_rready_o),.data_load_we_o(data_load_we_o),.data_load_addr_o(data_load_addr_o),.data_load_tag_o(data_load_tag_o),.data_load_be_o(data_load_be_o),.data_load_rdata_i(data_load_rdata_i),.data_load_tag_i(data_load_tag_i),.data_load_except_raised_i(data_load_except_raised_i),.data_load_except_code_i(data_load_except_code_i),.data_store_req_o(data_store_req_o),.data_store_gnt_i(data_store_gnt_i),.data_store_rvalid_i(data_store_rvalid_i),.data_store_rready_o(data_store_rready_o),.data_store_we_o(data_store_we_o),.data_store_addr_o(data_store_addr_o),.data_store_tag_o(data_store_tag_o),.data_store_be_o(data_store_be_o),.data_store_wdata_o(data_store_wdata_o),.data_store_tag_i(data_store_tag_i),.data_store_except_raised_i(data_store_except_raised_i),.data_store_except_code_i(data_store_except_code_i),.irq_i(irq_i),.irq_ack_o(irq_ack_o),.irq_id_o(irq_id_o),.fetch_enable_i(fetch_enable_i),.core_sleep_o(core_sleep_o),.probe_insert(probe_insert),.probe_index(probe_index),.ffq_obs(ffq_obs));
  reg [31:0] selected_instruction;
  reg selected_instruction_fault; reg [4:0] selected_instruction_code;
  always @* begin
    selected_instruction = 32'b0;
    selected_instruction_fault = 1; selected_instruction_code = 1;
    if (instr_addr_o[1:0] != 0) selected_instruction_code = 0;
    else if (instr_addr_o < 64'd56) begin
      selected_instruction = 0;
      selected_instruction_fault = 0; selected_instruction_code = 31;
      case (instr_addr_o)
        64'h0000000000000000: selected_instruction = 32'h00001437;
        64'h0000000000000004: selected_instruction = 32'h000024b7;
        64'h0000000000000008: selected_instruction = 32'h04000913;
        64'h000000000000000c: selected_instruction = 32'h00043503;
        64'h0000000000000010: selected_instruction = 32'h00150593;
        64'h0000000000000014: selected_instruction = 32'h00b4b023;
        64'h0000000000000018: selected_instruction = 32'h00840413;
        64'h000000000000001c: selected_instruction = 32'h00848493;
        64'h0000000000000020: selected_instruction = 32'hfff90913;
        64'h0000000000000024: selected_instruction = 32'hfe0914e3;
        64'h0000000000000028: selected_instruction = 32'h200002b7;
        64'h000000000000002c: selected_instruction = 32'h1002829b;
        64'h0000000000000030: selected_instruction = 32'h00028023;
        64'h0000000000000034: selected_instruction = 32'h0000006f;
        default: ;
      endcase
    end
  end
  assign irq_i = 0;
  assign fetch_enable_i = 1;
  assign instr_except_raised_i = ifault[1];
  assign instr_except_code_i = icode1;
  assign data_load_except_raised_i = 0;
  assign data_load_except_code_i = (data_load_rvalid_i || invalid_code_nonzero[1]) ? 31 : 0;
  assign data_store_except_raised_i = 0;
  assign data_store_except_code_i = (data_store_rvalid_i || invalid_code_nonzero[2]) ? 31 : 0;
  // Native two-stage fetch pipeline: freeze with core response readiness.
  // SKIP_INS_ANS_REG=1 couples upstream grant to this same readiness.
  reg [1:0] iv, ifault; reg [31:0] ins0, ins1; reg [4:0] icode0, icode1;
  reg [0:0] gap_left;
  // Fetch gate (simulation only): always open, as on the gap 1 platform. LEN5 loses a misprediction
  // redirect that the fetch interface refuses, even for one cycle, when the commit unit flushes.
  reg [7:0] refusal_run;
  wire gate_open = 1'b1;
  always @(posedge clk_i) refusal_run <= (!rst_ni || gate_open) ? 8'd0
    : refusal_run + {7'd0, refusal_run != 8'hff};
  wire ipush = instr_req_o && instr_gnt_i;
  assign instr_gnt_i = instr_rready_o && gate_open;
  assign instr_rvalid_i = iv[1];
  assign instr_rdata_i = ins1;
  always @(posedge clk_i) begin
    if (!rst_ni) begin
      iv <= 0; ifault <= 0; ins0 <= 0; ins1 <= 0; icode0 <= 0; icode1 <= 0; gap_left <= 0;
    end else begin
      if (gap_left != 0) gap_left <= gap_left - 1;
      if (ipush) gap_left <= 0;
      if (mem_flush_o) begin iv <= 0; ifault <= 0; ins0 <= 0; ins1 <= 0; icode0 <= 0; icode1 <= 0; end
      else if (instr_rready_o) begin
        iv <= {iv[0], instr_req_o && gate_open};
        ins0 <= (instr_req_o && gate_open) ? selected_instruction : 0;
        ins1 <= ins0;
        ifault <= {ifault[0], instr_req_o && gate_open && selected_instruction_fault};
        icode0 <= (instr_req_o && gate_open) ? selected_instruction_code : 31;
        icode1 <= icode0;
      end
    end
  end
  // Enveloped data service (simulation only): random grants; replies in order, each
  // delivered a testbench-chosen number of cycles after its acceptance, or right after
  // the older reply ahead of it; flush never cancels data replies. Acceptance times and
  // per-tag sequence numbers are kept for the testbench monitors only.
  reg [3:0] lq_tag [0:7]; reg [63:0] lq_data [0:7]; reg [31:0] lq_due [0:7]; reg [31:0] lq_acc [0:7];
  reg [31:0] lq_seq [0:7]; reg [3:0] sq_tag [0:7]; reg [31:0] sq_due [0:7]; reg [31:0] sq_acc [0:7];
  reg [31:0] sq_seq [0:7]; reg [31:0] l_last [0:15]; reg [31:0] s_last [0:15];
  reg [3:0] lq_count, sq_count;
  reg [2:0] lq_head, lq_tail, sq_head, sq_tail;
  reg [31:0] now, l_seq, s_seq;
  wire l_push = data_load_req_o && data_load_gnt_i, l_pop = data_load_rvalid_i && data_load_rready_o;
  wire s_push = data_store_req_o && data_store_gnt_i, s_pop = data_store_rvalid_i && data_store_rready_o;
  assign data_load_gnt_i = rst_ni && load_gnt && lq_count != 4'd8;
  assign data_store_gnt_i = rst_ni && store_gnt && sq_count != 4'd8;
  assign data_load_rvalid_i = lq_count != 4'd0 && now >= lq_due[lq_head];
  assign data_store_rvalid_i = sq_count != 4'd0 && now >= sq_due[sq_head];
  assign data_load_tag_i = lq_tag[lq_head]; assign data_store_tag_i = sq_tag[sq_head];
  assign data_load_rdata_i = lq_data[lq_head];
  always @(posedge clk_i) begin
    if (!rst_ni) begin
      lq_count <= 0; sq_count <= 0; lq_head <= 0; lq_tail <= 0; sq_head <= 0; sq_tail <= 0;
      now <= 0; l_seq <= 0; s_seq <= 0;
      // Without a reply, the tag buses carry the reset value or an earlier request's tag.
      for (int i = 0; i < 8; i++) begin lq_tag[i] <= 0; sq_tag[i] <= 0; end
    end else begin
      now <= now + 32'd1;
      if (l_push) begin
        lq_tag[lq_tail] <= data_load_tag_o; lq_data[lq_tail] <= load_value; lq_acc[lq_tail] <= now;
        lq_due[lq_tail] <= now + {24'd0, load_lat}; lq_seq[lq_tail] <= l_seq; l_last[data_load_tag_o] <= l_seq;
        l_seq <= l_seq + 32'd1; lq_tail <= lq_tail + 3'd1;
      end
      if (s_push) begin
        sq_tag[sq_tail] <= data_store_tag_o; sq_acc[sq_tail] <= now;
        sq_due[sq_tail] <= now + {24'd0, store_lat}; sq_seq[sq_tail] <= s_seq; s_last[data_store_tag_o] <= s_seq;
        s_seq <= s_seq + 32'd1; sq_tail <= sq_tail + 3'd1;
      end
      if (l_pop) lq_head <= lq_head + 3'd1;
      if (s_pop) sq_head <= sq_head + 3'd1;
      lq_count <= lq_count + {3'd0, l_push} - {3'd0, l_pop};
      sq_count <= sq_count + {3'd0, s_push} - {3'd0, s_pop};
    end
  end
  // Observation only: aliases of existing nets.
  assign obs_ffq = ffq_obs; assign obs_insert = probe_insert; assign obs_index = probe_index;
  assign obs_fetch = ipush; assign obs_fetch_addr = instr_addr_o;
  assign obs_store = data_store_req_o; assign obs_store_addr = data_store_addr_o;
  assign obs_load = data_load_req_o; assign obs_flush = mem_flush_o;
  // Co-simulation only: observation aliases and shared initial register values.
  assign obs_core = {core_sleep_o, data_load_addr_o, data_load_be_o, data_load_req_o, data_load_rready_o, data_load_tag_o, data_load_we_o, data_store_addr_o, data_store_be_o, data_store_req_o, data_store_rready_o, data_store_tag_o, data_store_wdata_o, data_store_we_o, instr_addr_o, instr_req_o, instr_rready_o, instr_we_o, irq_ack_o, irq_id_o, mem_flush_o};
  assign obs_load_addr = data_load_addr_o; assign obs_store_data = data_store_wdata_o;
  assign obs_store_be = data_store_be_o;
  assign obs_service_ok = (!data_load_rvalid_i || data_load_rready_o) && (!data_store_rvalid_i || data_store_rready_o);
  initial begin
    if (!$value$plusargs("pinit_iv=%h", iv)) iv = '0;
    if (!$value$plusargs("pinit_ifault=%h", ifault)) ifault = '0;
    if (!$value$plusargs("pinit_ins0=%h", ins0)) ins0 = '0;
    if (!$value$plusargs("pinit_ins1=%h", ins1)) ins1 = '0;
    if (!$value$plusargs("pinit_icode0=%h", icode0)) icode0 = '0;
    if (!$value$plusargs("pinit_icode1=%h", icode1)) icode1 = '0;
    if (!$value$plusargs("pinit_gap_left=%h", gap_left)) gap_left = '0;
    if (!$value$plusargs("pinit_refusal_run=%h", refusal_run)) refusal_run = '0;
    if (!$value$plusargs("pinit_lq_count=%h", lq_count)) lq_count = '0;
    if (!$value$plusargs("pinit_sq_count=%h", sq_count)) sq_count = '0;
    if (!$value$plusargs("pinit_lq_head=%h", lq_head)) lq_head = '0;
    if (!$value$plusargs("pinit_lq_tail=%h", lq_tail)) lq_tail = '0;
    if (!$value$plusargs("pinit_sq_head=%h", sq_head)) sq_head = '0;
    if (!$value$plusargs("pinit_sq_tail=%h", sq_tail)) sq_tail = '0;
    if (!$value$plusargs("pinit_now=%h", now)) now = '0;
    if (!$value$plusargs("pinit_l_seq=%h", l_seq)) l_seq = '0;
    if (!$value$plusargs("pinit_s_seq=%h", s_seq)) s_seq = '0;
  end
endmodule
