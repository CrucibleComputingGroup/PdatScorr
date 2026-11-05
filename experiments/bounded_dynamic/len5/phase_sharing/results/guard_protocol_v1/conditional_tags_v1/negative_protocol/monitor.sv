module UniqueTagProtocol(
 input clk_i, rst_ni, flush_i,
 input issue_valid_i, issue_ready_i, input [4:0] issue_tag_i,
 input complete_valid_i, complete_ready_i, input [4:0] complete_tag_i
);
 always @* if ($initstate) assume (!rst_ni);
 reg [31:0] outstanding;
 wire allocate = issue_valid_i && issue_ready_i;
 wire release_tag = complete_valid_i && complete_ready_i;
 wire available = !outstanding[issue_tag_i] ||
                  (release_tag && complete_tag_i == issue_tag_i);
 always @* if (rst_ni && !flush_i && allocate) assert (available);
 always @(posedge clk_i or negedge rst_ni) begin
   if (!rst_ni) outstanding <= 0;
   else if (flush_i) outstanding <= 0;
   else begin
     if (release_tag) outstanding[complete_tag_i] <= 0;
     if (allocate) outstanding[issue_tag_i] <= 1;
   end
 end
endmodule
