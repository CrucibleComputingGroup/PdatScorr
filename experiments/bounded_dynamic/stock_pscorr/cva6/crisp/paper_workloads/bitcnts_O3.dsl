version 2

# Auto-generated DSL file for instruction subset optimization
#
# Program uses 25 instructions: ['add', 'addi', 'and', 'andi', 'auipc', 'beq', 'bge', 'bgeu', 'bltu', 'bne', 'jal', 'jalr', 'lbu', 'lui', 'lw', 'mul', 'mulhu', 'or', 'slli', 'sltiu', 'sltu', 'srai', 'srli', 'sub', 'sw']
# Required instruction set: RV32IM
# Forbidding 32 unused instructions

# Include required instruction extensions
include RV32I
include RV32M

# Forbid unused instructions (can be removed from hardware)
# These instructions are not used by the program
forbid BEQZ
forbid BLT
forbid BNEZ
forbid CALLDIV
forbid CALLDIVU
forbid CALLMUL
forbid CALLREM
forbid CALLREMU
forbid DIV
forbid DIVU
forbid J
forbid LB
forbid LH
forbid LHU
forbid LI
forbid MULH
forbid MULHSU
forbid MV
forbid NOP
forbid ORI
forbid REM
forbid REMU
forbid RET
forbid SB
forbid SH
forbid SLL
forbid SLT
forbid SLTI
forbid SRA
forbid SRL
forbid XOR
forbid XORI
