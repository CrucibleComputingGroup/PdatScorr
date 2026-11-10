# RV32I without shift instructions
# Shifts require shifter logic - removing should save area

version 2

include RV32I

# Forbid all shift instructions
forbid SLL
forbid SRL
forbid SRA
forbid SLLI
forbid SRLI
forbid SRAI
