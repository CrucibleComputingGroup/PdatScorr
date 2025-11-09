# ODC test fixture: Only one shift instruction allowed
# Expected: All 5 shamt bits should be constant (and thus ODCs)

version 2

include RV32I
forbid SLLI
forbid SRLI
forbid SRAI
forbid SLL
forbid SRL
forbid SRA

# Only allow SLLI with shamt=2 (binary: 00010)
include SLLI {shamt = 5'b00010}

# Expected ODCs:
# - shamt[4] = 0
# - shamt[3] = 0  
# - shamt[2] = 0
# - shamt[1] = 1
# - shamt[0] = 0
