// Baseline JSON SHA256: a917caae3c7a139b8c892a7271e95d962a83ab0a4c82e18c5b79232123193264
// Both copies share all inputs; all defined functional outputs are compared.
module TemporalMiter (input wire clk,
input wire rst,
input wire [1:0] init_mshr,
input wire [1:0] init_store,
input wire [1:0] init_uncache,
input wire [1:0] can_release,
input wire [43:0] init_addr,
input wire [11:0] init_alptr,
input wire [1:0] cache_grant,
input wire [185:0] cache_tag_in,
input wire [131:0] cache_data_in,
input wire [127:0] stored_line,
input wire [7:0] stored_byte_we,
input wire cache_flushing,
input wire recovery_valid,
input wire recovery_all,
input wire [5:0] recovery_head,
input wire [5:0] recovery_tail,
input wire [22:0] ic_request,
input wire write_busy,
input wire next_write_serial,
input wire [1:0] write_response,
input wire response_valid,
input wire [1:0] response_id,
input wire [63:0] response_data);
wire [1:0] ref_cache_req, cand_cache_req;
wire [1:0] ref_mshr_valid, cand_mshr_valid;
wire [197:0] ref_cache_out, cand_cache_out;
wire [43:0] ref_mshr_addr, cand_mshr_addr;
wire [9:0] ref_mshr_phase, cand_mshr_phase;
wire [127:0] ref_mshr_data, cand_mshr_data;
wire ref_flush_complete, cand_flush_complete;
wire [21:0] ref_memory_addr, cand_memory_addr;
wire [63:0] ref_memory_write_data, cand_memory_write_data;
wire ref_read_accept, cand_read_accept;
wire ref_write_accept, cand_write_accept;
wire [1:0] ref_allocated_id, cand_allocated_id;
wire [2:0] ref_ic_ack, cand_ic_ack;
wire [66:0] ref_ic_result, cand_ic_result;
MshrObserved reference(.clk(clk),
.rst(rst),
.init_mshr(init_mshr),
.init_store(init_store),
.init_uncache(init_uncache),
.can_release(can_release),
.init_addr(init_addr),
.init_alptr(init_alptr),
.cache_grant(cache_grant),
.cache_tag_in(cache_tag_in),
.cache_data_in(cache_data_in),
.stored_line(stored_line),
.stored_byte_we(stored_byte_we),
.cache_flushing(cache_flushing),
.recovery_valid(recovery_valid),
.recovery_all(recovery_all),
.recovery_head(recovery_head),
.recovery_tail(recovery_tail),
.ic_request(ic_request),
.write_busy(write_busy),
.next_write_serial(next_write_serial),
.write_response(write_response),
.response_valid(response_valid),
.response_id(response_id),
.response_data(response_data),
.cache_req(ref_cache_req),
.mshr_valid(ref_mshr_valid),
.cache_out(ref_cache_out),
.mshr_addr(ref_mshr_addr),
.mshr_phase(ref_mshr_phase),
.mshr_data(ref_mshr_data),
.flush_complete(ref_flush_complete),
.memory_addr(ref_memory_addr),
.memory_write_data(ref_memory_write_data),
.read_accept(ref_read_accept),
.write_accept(ref_write_accept),
.allocated_id(ref_allocated_id),
.ic_ack(ref_ic_ack),
.ic_result(ref_ic_result));
MshrCandidate candidate(.clk(clk),
.rst(rst),
.init_mshr(init_mshr),
.init_store(init_store),
.init_uncache(init_uncache),
.can_release(can_release),
.init_addr(init_addr),
.init_alptr(init_alptr),
.cache_grant(cache_grant),
.cache_tag_in(cache_tag_in),
.cache_data_in(cache_data_in),
.stored_line(stored_line),
.stored_byte_we(stored_byte_we),
.cache_flushing(cache_flushing),
.recovery_valid(recovery_valid),
.recovery_all(recovery_all),
.recovery_head(recovery_head),
.recovery_tail(recovery_tail),
.ic_request(ic_request),
.write_busy(write_busy),
.next_write_serial(next_write_serial),
.write_response(write_response),
.response_valid(response_valid),
.response_id(response_id),
.response_data(response_data),
.cache_req(cand_cache_req),
.mshr_valid(cand_mshr_valid),
.cache_out(cand_cache_out),
.mshr_addr(cand_mshr_addr),
.mshr_phase(cand_mshr_phase),
.mshr_data(cand_mshr_data),
.flush_complete(cand_flush_complete),
.memory_addr(cand_memory_addr),
.memory_write_data(cand_memory_write_data),
.read_accept(cand_read_accept),
.write_accept(cand_write_accept),
.allocated_id(cand_allocated_id),
.ic_ack(cand_ic_ack),
.ic_result(cand_ic_result));
ReadServiceContract #(.MIN_SPACING(3),.MAX_LATENCY(9),.ORDERED(1)) service(
  .clk(clk),.rst(rst),.read_accept(ref_read_accept),.allocated_id(ref_allocated_id),
  .response_valid(response_valid),.response_id(response_id));
always @* begin
  assert(ref_cache_req == cand_cache_req);
  assert(ref_mshr_valid == cand_mshr_valid);
  assert(ref_cache_out == cand_cache_out);
  assert(ref_mshr_addr == cand_mshr_addr);
  assert(ref_mshr_phase == cand_mshr_phase);
  assert(ref_mshr_data == cand_mshr_data);
  assert(ref_flush_complete == cand_flush_complete);
  assert(ref_memory_addr == cand_memory_addr);
  assert(ref_memory_write_data == cand_memory_write_data);
  assert(ref_read_accept == cand_read_accept);
  assert(ref_write_accept == cand_write_accept);
  assert(ref_allocated_id == cand_allocated_id);
  assert(ref_ic_ack == cand_ic_ack);
  assert(ref_ic_result == cand_ic_result);
end
endmodule
// Formal-only history monitor. Assumes external service, not the ODC conclusion.
// Responses may not precede their acceptance edge. Deadline counts cycles
// from that edge: acceptance at t permits responses t+1,...,t+MAX_LATENCY.
module ReadServiceContract #(
    parameter integer ID_WIDTH=2,
    parameter integer MIN_SPACING=2,
    parameter integer MAX_LATENCY=3,
    parameter bit ORDERED=1
)(
    input logic clk, rst, read_accept,
    input logic [ID_WIDTH-1:0] allocated_id,
    input logic response_valid,
    input logic [ID_WIDTH-1:0] response_id
);
    localparam integer N=1<<ID_WIDTH;
    localparam integer AGE_WIDTH=$clog2(MAX_LATENCY+1);
    localparam integer GAP_WIDTH=$clog2(MIN_SPACING+1);
    logic [ID_WIDTH:0] count, next_count;
    logic [ID_WIDTH-1:0] queue_id[N], next_id[N];
    logic [AGE_WIDTH-1:0] queue_age[N], next_age[N];
    logic [GAP_WIDTH-1:0] gap;
    integer match_index;
    logic found;
    logic initialized=0;
    always_ff @(posedge clk) initialized<=1;

    always_comb begin
        if (!initialized) assume(rst);
        if (rst) begin
            assume(!read_accept);
            assume(!response_valid);
        end else begin
            if (read_accept) assume(gap >= MIN_SPACING-1);
            if (response_valid) begin
                assume(count != 0);
                assume(found);
                if (ORDERED) assume(response_id == queue_id[0]);
            end
            for (integer j=0;j<N;j++) begin
                if (j<count) begin
                    assume(queue_age[j] < MAX_LATENCY);
                    if (queue_age[j] == MAX_LATENCY-1)
                        assume(response_valid && response_id == queue_id[j]);
                end
            end
        end
    end

    always_comb begin
        found=0;
        match_index=0;
        for (integer j=0;j<N;j++) begin
            if (j<count && response_id==queue_id[j]) begin
                found=1;
                match_index=j;
            end
            next_id[j]=queue_id[j];
            next_age[j]=queue_age[j]+1'b1;
        end
        next_count=count;
        if (response_valid) begin
            for (integer j=0;j<N-1;j++) begin
                if (j>=match_index) begin
                    next_id[j]=queue_id[j+1];
                    next_age[j]=queue_age[j+1]+1'b1;
                end
            end
            next_count=count-1'b1;
        end
        if (read_accept) begin
            next_id[next_count]=allocated_id;
            next_age[next_count]='0;
            next_count=next_count+1'b1;
        end
    end
    always_ff @(posedge clk) begin
        if (rst) begin
            count<=0;
            gap<=MIN_SPACING;
            for (integer j=0;j<N;j++) begin
                queue_id[j]<=0;
                queue_age[j]<=0;
            end
        end else begin
            count<=next_count;
            for (integer j=0;j<N;j++) begin
                queue_id[j]<=next_id[j];
                queue_age[j]<=next_age[j];
            end
            if (read_accept) gap<=0;
            else if (gap<MIN_SPACING) gap<=gap+1'b1;
        end
    end
endmodule

