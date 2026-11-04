import CacheSystemTypes::*;
module MshrTimingProof(input logic [0:0] clk,
input logic [0:0] rst,
input logic [1:0] init_mshr,
input logic [1:0] init_store,
input logic [1:0] init_uncache,
input logic [1:0] can_release,
input logic [43:0] init_addr,
input logic [11:0] init_alptr,
input logic [1:0] cache_grant,
input logic [185:0] cache_tag_in,
input logic [131:0] cache_data_in,
input logic [127:0] stored_line,
input logic [7:0] stored_byte_we,
input logic [0:0] cache_flushing,
input logic [0:0] recovery_valid,
input logic [0:0] recovery_all,
input logic [5:0] recovery_head,
input logic [5:0] recovery_tail,
input logic [22:0] ic_request,
input logic [0:0] write_busy,
input logic [0:0] next_write_serial,
input logic [1:0] write_response,
input logic [0:0] response_valid,
input logic [1:0] response_id,
input logic [63:0] response_data);
logic [1:0] cache_req;
logic [1:0] mshr_valid;
logic [197:0] cache_out;
logic [43:0] mshr_addr;
logic [9:0] mshr_phase;
logic [127:0] mshr_data;
logic [0:0] flush_complete;
logic [21:0] memory_addr;
logic [63:0] memory_write_data;
logic [0:0] read_accept;
logic [0:0] write_accept;
logic [1:0] allocated_id;
logic [2:0] ic_ack;
logic [66:0] ic_result;
MshrObserved dut(.*);
ReadServiceContract #(.MIN_SPACING(3),.MAX_LATENCY(5),.ORDERED(1)) service(.*);
logic [1:0] accepted, returned; logic seen_three;
always_ff @(posedge clk) begin
  if (rst) begin accepted<=0; returned<=0; seen_three<=0; end
  else begin
    if(read_accept) accepted<=accepted+1'b1;
    if(response_valid) returned<=returned+1'b1;
    if(read_accept && allocated_id==3) seen_three<=1;
  end
end
wire [1:0] saved0=dut.handler.mshr[0].memSerial;
wire [1:0] saved1=dut.handler.mshr[1].memSerial;
wire waiting0=dut.handler.mshr[0].phase==MSHR_PHASE_MISS_READ_MEM_RECEIVE;
wire waiting1=dut.handler.mshr[1].phase==MSHR_PHASE_MISS_READ_MEM_RECEIVE;
logic pending0,pending1;
always_comb begin
  pending0=0; pending1=0;
  for(integer j=0;j<4;j++) if(j<service.count) begin
    pending0 |= saved0==service.queue_id[j];
    pending1 |= saved1==service.queue_id[j];
  end
end
always_comb if(!rst) begin
  assert(!waiting0 || !response_valid || saved0[0]!=response_id[0] || saved0[1]==response_id[1]);
  assert(!waiting1 || !response_valid || saved1[0]!=response_id[0] || saved1[1]==response_id[1]);
  assert(service.count<=2);
  assert(allocated_id==accepted);
  assert(dut.ids.headPtr==accepted);
  assert(dut.ids.tailPtr==returned);
  assert((accepted-returned)==service.count[1:0]);
  assert(({1'b0,dut.ids.pointer.regCount}+service.count)==4);
  assert(!waiting0 || pending0);
  assert(!waiting1 || pending1);
  assert(dut.ids.freeList[0]==2'd0);
  if(0<service.count) assert(service.queue_id[0]==(returned+2'd0));
  assert(dut.ids.freeList[1]==2'd1);
  if(1<service.count) assert(service.queue_id[1]==(returned+2'd1));
  assert(dut.ids.freeList[2]==2'd2);
  if(2<service.count) assert(service.queue_id[2]==(returned+2'd2));
  assert(dut.ids.freeList[3]==2'd3);
  if(3<service.count) assert(service.queue_id[3]==(returned+2'd3));
  cover(service.count==2 && waiting0 && waiting1);
  cover(waiting0 && response_valid && saved0[1]!=response_id[1]);
  cover(waiting1 && response_valid && saved1[1]!=response_id[1]);
  cover(seen_three && read_accept && allocated_id==0);
end
endmodule
