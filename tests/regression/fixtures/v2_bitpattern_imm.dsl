# V2 with bit patterns on immediate fields
# Tests 12-bit immediate patterns

version 2

include ADDI {imm = 12'b000000000000}  # imm=0
include ADDI {imm = 12'b000000000001}  # imm=1
include ADDI {imm = 12'b000000000010}  # imm=2
include ADDI {imm = 12'b000000000100}  # imm=4
include ADDI {imm = 12'b000000001000}  # imm=8
