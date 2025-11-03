# V2 sequential semantics test
# Tests that order matters in v2

version 2

include RV32I
forbid ADD
include ADD {rd = x0}

forbid ADDI
include ADDI {imm = 12'b000000000001}
