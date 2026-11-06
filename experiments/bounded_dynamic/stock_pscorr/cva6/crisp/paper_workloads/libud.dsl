version 2

# Auto-generated DSL file for instruction subset optimization
#
# Program uses 24 instructions: ['add', 'addi', 'andi', 'auipc', 'beq', 'bge', 'bgeu', 'blt', 'bltu', 'bne', 'div', 'jal', 'jalr', 'lbu', 'lui', 'lw', 'mul', 'or', 'slli', 'sltiu', 'srli', 'sub', 'sw', 'xori']
# Required instruction set: RV32IM
# Forbidding 33 unused instructions

# Include required instruction extensions
include RV32I
include RV32M

# Forbid unused instructions (can be removed from hardware)
# These instructions are not used by the program
forbid AND
forbid BEQZ
forbid BNEZ
forbid CALLDIV
forbid CALLDIVU
forbid CALLMUL
forbid CALLREM
forbid CALLREMU
forbid DIVU
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
forbid REMU
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
forbid XOR
