module EUDomainProof(input [31:0] instruction_i, output [2:0] assigned_eu);
DecoderBase dut(.instruction_i(instruction_i), .assigned_eu_o(assigned_eu));
always @* begin
assert(assigned_eu[2] == 0);
end
endmodule
