
module HarvardLookupTest;
  import len5_pkg::*;
  logic clk=0;
  always #5 clk=~clk;
  byte unsigned reference [0:55];
  logic [37:0] answer;
  logic [31:0] expected;
  logic [63:0] address;
  int checks=0;
  int ret;
  memory_bare_emu #(.PIPE_NUM(2), .SKIP_INS_ANS_REG(1), .SKIP_DATA_ANS_REG(0)) dut (
    .clk_i(clk), .rst_ni(1'b0), .instr_flush_i(1'b0),
    .mem_file_i("/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build/harvard_streaming_v1/data.hex"), .mem_dump_file_i("unused"),
    .instr_valid_i(1'b0), .instr_ready_i(1'b1), .instr_addr_i(64'b0),
    .data_load_valid_i(1'b0), .data_load_ready_i(1'b1), .data_load_addr_i(64'b0),
    .data_load_be_i(8'hff), .data_load_tag_i('0),
    .data_store_valid_i(1'b0), .data_store_ready_i(1'b1), .data_store_we_i(1'b0),
    .data_store_addr_i(64'b0), .data_store_tag_i('0), .data_store_be_i(8'hff), .data_store_wdata_i(64'b0)
  );
  initial begin
    $readmemh("/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build/harvard_streaming_v1/instruction.hex", reference);
    #1;
    for (int i=0; i<68; i++) begin
      if (i<64) address=64'(i);
      else case(i)
        64: address=64'h1000;
        65: address=64'h1001;
        66: address=64'hfffffffffffffffc;
        67: address=64'hffffffffffffffff;
      endcase
      answer=dut.lookup_instruction_rom(address);
      if (address[1:0] != 0) begin
        assert(answer[37:6]==0 && answer[5] && answer[4:0]==E_I_ADDR_MISALIGNED)
          else $fatal(1,"Misaligned ROM response incorrect at %h",address);
      end else if (address >= 56) begin
        assert(answer[37:6]==0 && answer[5] && answer[4:0]==E_I_ACCESS_FAULT)
          else $fatal(1,"Unmapped ROM response incorrect at %h",address);
      end else begin
        expected={reference[address+3],reference[address+2],reference[address+1],reference[address]};
        assert(answer[37:6]==expected && !answer[5] && answer[4:0]==E_UNKNOWN)
          else $fatal(1,"Mapped ROM response incorrect at %h",address);
      end
      checks++;
    end
    ret=dut.mem.WriteW(0,32'hdeadbeef);
    assert(ret==0) else $fatal(1,"Data write failed");
    ret=dut.mem.ReadW(0);
    assert(ret==0 && dut.mem.read_word==32'hdeadbeef) else $fatal(1,"Data write not stored");
    answer=dut.lookup_instruction_rom(0);
    expected={reference[3],reference[2],reference[1],reference[0]};
    assert(answer[37:6]==expected && !answer[5]) else $fatal(1,"Data write changed instruction ROM");
    checks++;
    ret=dut.mem.WriteW(64'h1000,32'hfeedcafe);
    answer=dut.lookup_instruction_rom(64'h1000);
    assert(ret==0 && answer[37:6]==0 && answer[5] && answer[4:0]==E_I_ACCESS_FAULT)
      else $fatal(1,"Data address became executable");
    checks++;
    $display("HARVARD_LOOKUP_PASS checks=%0d", checks);
    $finish;
  end
endmodule
