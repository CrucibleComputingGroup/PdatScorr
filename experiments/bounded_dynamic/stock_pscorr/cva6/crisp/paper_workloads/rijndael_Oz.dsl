version 2

# Auto-generated DSL file for instruction subset optimization
#
# Program uses 30 instructions: ['add', 'addi', 'and', 'andi', 'auipc', 'beq', 'bge', 'bgeu', 'blt', 'bltu', 'bne', 'divu', 'jal', 'jalr', 'lbu', 'lui', 'lw', 'mul', 'or', 'remu', 'sb', 'slli', 'sltiu', 'sltu', 'srai', 'srli', 'sub', 'sw', 'xor', 'xori']
# Required instruction set: RV32IM
# Forbidding 27 unused instructions

# Include required instruction extensions
include RV32I
include RV32M

# Forbid unused instructions (can be removed from hardware)
# These instructions are not used by the program
forbid BEQZ
forbid BNEZ
forbid CALLDIV
forbid CALLDIVU
forbid CALLMUL
forbid CALLREM
forbid CALLREMU
forbid DIV
forbid J
forbid LB
forbid LH
forbid LHU
forbid LI
forbid MULH
forbid MULHSU
forbid MULHU
forbid MV
forbid NOP
forbid ORI
forbid REM
forbid RET
forbid SH
forbid SLL
forbid SLT
forbid SLTI
forbid SRA
forbid SRL
