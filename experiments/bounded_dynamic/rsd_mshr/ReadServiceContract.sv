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
