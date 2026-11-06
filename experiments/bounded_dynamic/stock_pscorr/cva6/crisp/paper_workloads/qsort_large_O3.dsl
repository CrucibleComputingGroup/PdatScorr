version 2

# Auto-generated DSL file for instruction subset optimization
#
# Program uses 23 instructions: ['add', 'addi', 'andi', 'auipc', 'beq', 'bge', 'bgeu', 'blt', 'bltu', 'bne', 'jal', 'jalr', 'lui', 'lw', 'mul', 'mulh', 'or', 'slli', 'sltiu', 'sltu', 'srai', 'srli', 'sw']
# Required instruction set: RV32IM
# Forbidding 34 unused instructions

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
forbid DIV
forbid DIVU
forbid J
forbid LB
forbid LBU
forbid LH
forbid LHU
forbid LI
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
forbid SRA
forbid SRL
forbid SUB
forbid XOR
forbid XORI
