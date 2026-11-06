version 2

# Auto-generated DSL file for instruction subset optimization
#
# Program uses 16 instructions: ['add', 'addi', 'auipc', 'beq', 'bge', 'blt', 'bne', 'jal', 'jalr', 'lui', 'lw', 'slli', 'sltiu', 'sub', 'sw', 'xori']
# Required instruction set: RV32I
# Forbidding 33 unused instructions

# Include required instruction extensions
include RV32I

# Forbid unused instructions (can be removed from hardware)
# These instructions are not used by the program
forbid AND
forbid ANDI
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
forbid LBU
forbid LH
forbid LHU
forbid LI
forbid MV
forbid NOP
forbid OR
forbid ORI
forbid RET
forbid SB
forbid SH
forbid SLL
forbid SLT
forbid SLTI
forbid SLTU
forbid SRA
forbid SRAI
forbid SRL
forbid SRLI
forbid XOR
