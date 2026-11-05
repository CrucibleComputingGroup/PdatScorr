module EUProof(input [2:0] registered_eu, input [0:0] other_inputs, output [0:0] mul_valid, output [0:0] div_valid);
NativeEUDispatch dut(.registered_eu(registered_eu), .other_inputs(other_inputs), .mul_valid(mul_valid), .div_valid(div_valid));
always @* begin
assert(!mul_valid && !div_valid);
end
endmodule
