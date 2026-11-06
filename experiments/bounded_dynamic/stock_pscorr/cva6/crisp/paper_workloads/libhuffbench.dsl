version 2

# Auto-generated DSL file for instruction subset optimization
#
# Program uses 27 instructions: ['add', 'addi', 'and', 'andi', 'auipc', 'beq', 'bge', 'bgeu', 'blt', 'bltu', 'bne', 'jal', 'jalr', 'lbu', 'lui', 'lw', 'or', 'ori', 'sb', 'sll', 'slli', 'sltiu', 'sltu', 'srai', 'srli', 'sub', 'sw']
# Required instruction set: RV32I
# Forbidding 22 unused instructions

# Include required instruction extensions
include RV32I

# Forbid unused instructions (can be removed from hardware)
# These instructions are not used by the program
forbid BEQZ
forbid BNEZ
forbid CALLDIV
forbid CALLDIVU
forbid CALLMUL
forbid CALLREM
forbid CALLREMU
forbid J
forbid LB
forbid LH
forbid LHU
forbid LI
forbid MV
forbid NOP
forbid RET
forbid SH
forbid SLT
forbid SLTI
forbid SRA
forbid SRL
forbid XOR
forbid XORI
