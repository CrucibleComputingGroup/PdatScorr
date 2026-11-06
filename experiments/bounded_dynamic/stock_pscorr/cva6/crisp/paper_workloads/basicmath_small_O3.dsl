version 2

# Auto-generated DSL file for instruction subset optimization
#
# Program uses 26 instructions: ['add', 'addi', 'andi', 'auipc', 'beq', 'bge', 'bgeu', 'blt', 'bltu', 'bne', 'div', 'jal', 'jalr', 'lui', 'lw', 'mul', 'mulh', 'mulhu', 'or', 'slli', 'sltiu', 'srai', 'srli', 'sub', 'sw', 'xor']
# Required instruction set: RV32IM
# Forbidding 31 unused instructions

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
forbid LBU
forbid LH
forbid LHU
forbid LI
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
forbid SLTU
forbid SRA
forbid SRL
forbid XORI
