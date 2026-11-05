module EUDomainProof(input [31:0] instruction_i, output [2:0] assigned_eu);
DecoderBase dut(.instruction_i(instruction_i), .assigned_eu_o(assigned_eu));
always @* begin
assume((instruction_i == 0) || (instruction_i == 32'h0000006f) || (instruction_i == 32'h00001437) || (instruction_i == 32'h000024b7) || (instruction_i == 32'h00028023) || (instruction_i == 32'h00043503) || (instruction_i == 32'h00150593) || (instruction_i == 32'h00840413) || (instruction_i == 32'h00848493) || (instruction_i == 32'h00b4b023) || (instruction_i == 32'h04000913) || (instruction_i == 32'h1002829b) || (instruction_i == 32'h200002b7) || (instruction_i == 32'hfe0914e3) || (instruction_i == 32'hfff90913));
assert(assigned_eu[2] == 0);
end
endmodule
