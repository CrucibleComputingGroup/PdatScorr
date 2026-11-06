version 2

# Auto-generated DSL file for instruction subset optimization
#
# Program uses 23 instructions: ['add', 'addi', 'andi', 'auipc', 'beq', 'bge', 'blt', 'bne', 'jal', 'jalr', 'lbu', 'lui', 'lw', 'or', 'sb', 'slli', 'sltiu', 'sltu', 'srai', 'srli', 'sub', 'sw', 'xor']
# Required instruction set: RV32I
# Forbidding 26 unused instructions

# Include required instruction extensions
include RV32I

# Forbid unused instructions (can be removed from hardware)
# These instructions are not used by the program
forbid AND
forbid BEQZ
forbid BGEU
forbid BLTU
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
forbid ORI
forbid RET
forbid SH
forbid SLL
forbid SLT
forbid SLTI
forbid SRA
forbid SRL
forbid XORI
