version 2

# Auto-generated DSL file for instruction subset optimization
#
# Program uses 34 instructions: ['add', 'addi', 'and', 'andi', 'auipc', 'beq', 'bge', 'bgeu', 'blt', 'bltu', 'bne', 'jal', 'jalr', 'lb', 'lbu', 'lh', 'lhu', 'lui', 'lw', 'mul', 'or', 'ori', 'sb', 'sh', 'sll', 'slli', 'sltiu', 'sltu', 'sra', 'srai', 'srli', 'sub', 'sw', 'xori']
# Required instruction set: RV32IM
# Forbidding 23 unused instructions

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
forbid DIVU
forbid J
forbid LI
forbid MULH
forbid MULHSU
forbid MULHU
forbid MV
forbid NOP
forbid REM
forbid REMU
forbid RET
forbid SLT
forbid SLTI
forbid SRL
forbid XOR
