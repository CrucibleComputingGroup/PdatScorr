# ODC test fixture: Shifts with power-of-2 amounts (0, 1, 2, 4, 8)
# Expected: Bits [4:3] should be constant 0 (max shift is 8 = 0b01000)

version 2

include RV32I
forbid SLLI
forbid SRLI
forbid SRAI

# Power-of-2 shift amounts
include SLLI {shamt = 5'b00000}  # 0
include SLLI {shamt = 5'b00001}  # 1
include SLLI {shamt = 5'b00010}  # 2
include SLLI {shamt = 5'b00100}  # 4
include SLLI {shamt = 5'b01000}  # 8

# Expected ODCs:
# - shamt[4] = 0 (max value is 8, so bit 4 never set)
# - shamt[3] = varies (set for shamt=8, not for others) - NOT an ODC
# - shamt[2:0] = varies - NOT ODCs
