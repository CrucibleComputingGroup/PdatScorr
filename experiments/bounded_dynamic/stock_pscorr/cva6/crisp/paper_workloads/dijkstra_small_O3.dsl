version 2

# Auto-generated DSL file for instruction subset optimization
#
# Program uses 19 instructions: ['add', 'addi', 'andi', 'auipc', 'beq', 'bge', 'bne', 'jal', 'jalr', 'lui', 'lw', 'mul', 'mulh', 'slli', 'slti', 'srai', 'srli', 'sub', 'sw']
# Required instruction set: RV32IM
# Forbidding 38 unused instructions

# Include required instruction extensions
include RV32I
include RV32M

# Forbid unused instructions (can be removed from hardware)
# These instructions are not used by the program
forbid AND
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
forbid LBU
forbid LH
forbid LHU
forbid LI
forbid MULHSU
forbid MULHU
forbid MV
forbid NOP
forbid OR
forbid ORI
forbid REM
forbid REMU
forbid RET
forbid SB
forbid SH
forbid SLL
forbid SLT
forbid SLTIU
forbid SLTU
forbid SRA
forbid SRL
forbid XOR
forbid XORI
