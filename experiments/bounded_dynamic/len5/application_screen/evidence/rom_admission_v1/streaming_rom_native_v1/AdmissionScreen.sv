module AdmissionScreen(input wire clk_i, rst_ni,
  input wire [3:0] instruction_choice, input wire [63:0] load_value,
  input wire [2:0] invalid_code_nonzero, input wire [31:0] instruction_fault_data);
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
  reg selected_instruction_fault; reg [4:0] selected_instruction_code;
  always @* begin
    selected_instruction = instruction_fault_data;
    selected_instruction_fault = 1; selected_instruction_code = 1;
    if (instr_addr_o[1:0] != 0) selected_instruction_code = 0;
    else if (instr_addr_o < 64'd4736) begin
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
        64'h0000000000001008: selected_instruction = 32'h7f487c15;
        64'h000000000000100c: selected_instruction = 32'h9e3779b9;
        64'h0000000000001010: selected_instruction = 32'hfe90f82a;
        64'h0000000000001014: selected_instruction = 32'h3c6ef372;
        64'h0000000000001018: selected_instruction = 32'h7dd9743f;
        64'h000000000000101c: selected_instruction = 32'hdaa66d2c;
        64'h0000000000001020: selected_instruction = 32'hfd21f054;
        64'h0000000000001024: selected_instruction = 32'h78dde6e5;
        64'h0000000000001028: selected_instruction = 32'h7c7e6c69;
        64'h000000000000102c: selected_instruction = 32'h1715609f;
        64'h0000000000001030: selected_instruction = 32'hfbb2e87e;
        64'h0000000000001034: selected_instruction = 32'hb54cda58;
        64'h0000000000001038: selected_instruction = 32'h7b076493;
        64'h000000000000103c: selected_instruction = 32'h53845412;
        64'h0000000000001040: selected_instruction = 32'hfa43e0a8;
        64'h0000000000001044: selected_instruction = 32'hf1bbcdcb;
        64'h0000000000001048: selected_instruction = 32'h798c5cbd;
        64'h000000000000104c: selected_instruction = 32'h8ff34785;
        64'h0000000000001050: selected_instruction = 32'hf8fcd8d2;
        64'h0000000000001054: selected_instruction = 32'h2e2ac13e;
        64'h0000000000001058: selected_instruction = 32'h782554e7;
        64'h000000000000105c: selected_instruction = 32'hcc623af8;
        64'h0000000000001060: selected_instruction = 32'hf765d0fc;
        64'h0000000000001064: selected_instruction = 32'h6a99b4b1;
        64'h0000000000001068: selected_instruction = 32'h76d24d11;
        64'h000000000000106c: selected_instruction = 32'h08d12e6b;
        64'h0000000000001070: selected_instruction = 32'hf60ec926;
        64'h0000000000001074: selected_instruction = 32'ha708a824;
        64'h0000000000001078: selected_instruction = 32'h7543453b;
        64'h000000000000107c: selected_instruction = 32'h454021de;
        64'h0000000000001080: selected_instruction = 32'hf487c150;
        64'h0000000000001084: selected_instruction = 32'he3779b97;
        64'h0000000000001088: selected_instruction = 32'h73d03d65;
        64'h000000000000108c: selected_instruction = 32'h81af1551;
        64'h0000000000001090: selected_instruction = 32'hf318b97a;
        64'h0000000000001094: selected_instruction = 32'h1fe68f0a;
        64'h0000000000001098: selected_instruction = 32'h72a1358f;
        64'h000000000000109c: selected_instruction = 32'hbe1e08c4;
        64'h00000000000010a0: selected_instruction = 32'hf1f9b1a4;
        64'h00000000000010a4: selected_instruction = 32'h5c55827d;
        64'h00000000000010a8: selected_instruction = 32'h71362db9;
        64'h00000000000010ac: selected_instruction = 32'hfa8cfc37;
        64'h00000000000010b0: selected_instruction = 32'hf04aa9ce;
        64'h00000000000010b4: selected_instruction = 32'h98c475f0;
        64'h00000000000010b8: selected_instruction = 32'h6f9f25e3;
        64'h00000000000010bc: selected_instruction = 32'h36fbefaa;
        64'h00000000000010c0: selected_instruction = 32'heecba1f8;
        64'h00000000000010c4: selected_instruction = 32'hd5336963;
        64'h00000000000010c8: selected_instruction = 32'h6e741e0d;
        64'h00000000000010cc: selected_instruction = 32'h736ae31d;
        64'h00000000000010d0: selected_instruction = 32'heda49a22;
        64'h00000000000010d4: selected_instruction = 32'h11a25cd6;
        64'h00000000000010d8: selected_instruction = 32'h6ced1637;
        64'h00000000000010dc: selected_instruction = 32'hafd9d690;
        64'h00000000000010e0: selected_instruction = 32'hec1d924c;
        64'h00000000000010e4: selected_instruction = 32'h4e115049;
        64'h00000000000010e8: selected_instruction = 32'h6b4a0e61;
        64'h00000000000010ec: selected_instruction = 32'hec48ca03;
        64'h00000000000010f0: selected_instruction = 32'hea868a76;
        64'h00000000000010f4: selected_instruction = 32'h8a8043bc;
        64'h00000000000010f8: selected_instruction = 32'h6a3b068b;
        64'h00000000000010fc: selected_instruction = 32'h28b7bd76;
        64'h0000000000001100: selected_instruction = 32'he90f82a0;
        64'h0000000000001104: selected_instruction = 32'hc6ef372f;
        64'h0000000000001108: selected_instruction = 32'h68dbfeb5;
        64'h000000000000110c: selected_instruction = 32'h6526b0e9;
        64'h0000000000001110: selected_instruction = 32'he7a07aca;
        64'h0000000000001114: selected_instruction = 32'h035e2aa2;
        64'h0000000000001118: selected_instruction = 32'h6768f6df;
        64'h000000000000111c: selected_instruction = 32'ha195a45c;
        64'h0000000000001120: selected_instruction = 32'he63172f4;
        64'h0000000000001124: selected_instruction = 32'h3fcd1e15;
        64'h0000000000001128: selected_instruction = 32'h6589ef09;
        64'h000000000000112c: selected_instruction = 32'hde0497cf;
        64'h0000000000001130: selected_instruction = 32'he5426b1e;
        64'h0000000000001134: selected_instruction = 32'h7c3c1188;
        64'h0000000000001138: selected_instruction = 32'h6416e733;
        64'h000000000000113c: selected_instruction = 32'h1a738b42;
        64'h0000000000001140: selected_instruction = 32'he3f36348;
        64'h0000000000001144: selected_instruction = 32'hb8ab04fb;
        64'h0000000000001148: selected_instruction = 32'h62bfdf5d;
        64'h000000000000114c: selected_instruction = 32'h56e27eb5;
        64'h0000000000001150: selected_instruction = 32'he26c5b72;
        64'h0000000000001154: selected_instruction = 32'hf519f86e;
        64'h0000000000001158: selected_instruction = 32'h61d4d787;
        64'h000000000000115c: selected_instruction = 32'h93517228;
        64'h0000000000001160: selected_instruction = 32'he095539c;
        64'h0000000000001164: selected_instruction = 32'h3188ebe1;
        64'h0000000000001168: selected_instruction = 32'h604dcfb1;
        64'h000000000000116c: selected_instruction = 32'hcfc0659b;
        64'h0000000000001170: selected_instruction = 32'hdf3e4bc6;
        64'h0000000000001174: selected_instruction = 32'h6df7df54;
        64'h0000000000001178: selected_instruction = 32'h5ef2c7db;
        64'h000000000000117c: selected_instruction = 32'h0c2f590e;
        64'h0000000000001180: selected_instruction = 32'hdd9743f0;
        64'h0000000000001184: selected_instruction = 32'haa66d2c7;
        64'h0000000000001188: selected_instruction = 32'h5d23c005;
        64'h000000000000118c: selected_instruction = 32'h489e4c81;
        64'h0000000000001190: selected_instruction = 32'hdce83c1a;
        64'h0000000000001194: selected_instruction = 32'he6d5c63a;
        64'h0000000000001198: selected_instruction = 32'h5bb0b82f;
        64'h000000000000119c: selected_instruction = 32'h850d3ff4;
        64'h00000000000011a0: selected_instruction = 32'hdb493444;
        64'h00000000000011a4: selected_instruction = 32'h2344b9ad;
        64'h00000000000011a8: selected_instruction = 32'h5a01b059;
        64'h00000000000011ac: selected_instruction = 32'hc17c3367;
        64'h00000000000011b0: selected_instruction = 32'hd9da2c6e;
        64'h00000000000011b4: selected_instruction = 32'h5fb3ad20;
        64'h00000000000011b8: selected_instruction = 32'h596ea883;
        64'h00000000000011bc: selected_instruction = 32'hfdeb26da;
        64'h00000000000011c0: selected_instruction = 32'hd83b2498;
        64'h00000000000011c4: selected_instruction = 32'h9c22a093;
        64'h00000000000011c8: selected_instruction = 32'h57e7a0ad;
        64'h00000000000011cc: selected_instruction = 32'h3a5a1a4d;
        64'h00000000000011d0: selected_instruction = 32'hd6941cc2;
        64'h00000000000011d4: selected_instruction = 32'hd8919406;
        64'h00000000000011d8: selected_instruction = 32'h565c98d7;
        64'h00000000000011dc: selected_instruction = 32'h76c90dc0;
        64'h00000000000011e0: selected_instruction = 32'hd50d14ec;
        64'h00000000000011e4: selected_instruction = 32'h15008779;
        64'h00000000000011e8: selected_instruction = 32'h54c59101;
        64'h00000000000011ec: selected_instruction = 32'hb3380133;
        64'h00000000000011f0: selected_instruction = 32'hd4760d16;
        64'h00000000000011f4: selected_instruction = 32'h516f7aec;
        64'h00000000000011f8: selected_instruction = 32'h532a892b;
        64'h00000000000011fc: selected_instruction = 32'hefa6f4a6;
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
  wire gate_open = gap_left == 0;
  wire ipush = instr_req_o && instr_gnt_i;
  assign instr_gnt_i = instr_rready_o && gate_open;
  assign instr_rvalid_i = iv[1];
  assign instr_rdata_i = ins1;
  always @(posedge clk_i) begin
    if (!rst_ni) begin
      iv <= 0; ifault <= 0; ins0 <= 0; ins1 <= 0; icode0 <= 0; icode1 <= 0; gap_left <= 0;
    end else begin
      if (gap_left != 0) gap_left <= gap_left - 1;
      if (ipush) gap_left <= 1;
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
