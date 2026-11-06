version 2

# Auto-generated DSL file for instruction subset optimization
#
# Program uses 20 instructions: ['add', 'addi', 'andi', 'auipc', 'beq', 'bge', 'bne', 'jalr', 'lbu', 'lui', 'lw', 'mul', 'mulh', 'slli', 'sltiu', 'srai', 'srli', 'sub', 'sw', 'xori']
# Required instruction set: RV32IM
# Forbidding 37 unused instructions

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
forbid JAL
forbid LB
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
forbid SLTI
forbid SLTU
forbid SRA
forbid SRL
forbid XOR
