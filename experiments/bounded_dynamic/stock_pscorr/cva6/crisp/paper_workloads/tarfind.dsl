version 2

# Auto-generated DSL file for instruction subset optimization
#
# Program uses 23 instructions: ['add', 'addi', 'and', 'andi', 'auipc', 'beq', 'bge', 'bne', 'jal', 'jalr', 'lbu', 'lui', 'lw', 'mul', 'mulhu', 'sb', 'slli', 'sltiu', 'sltu', 'srai', 'srli', 'sub', 'sw']
# Required instruction set: RV32IM
# Forbidding 34 unused instructions

# Include required instruction extensions
include RV32I
include RV32M

# Forbid unused instructions (can be removed from hardware)
# These instructions are not used by the program
forbid BEQZ
forbid BGEU
forbid BLT
forbid BLTU
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
forbid OR
forbid ORI
forbid REM
forbid REMU
forbid RET
forbid SH
forbid SLL
forbid SLT
forbid SLTI
forbid SRA
forbid SRL
forbid XOR
forbid XORI
