version 2

# Embench cubic, compiled for RV64IM (see make_workload_crisp.py).
# Uses 25 RV64IM instructions: ADD ADDI ADDIW AUIPC BEQ BGE BLT BLTU BNE JAL JALR LBU LD LUI LW MUL SB SD SLLI SLTI SLTU SRLI SW XOR XORI
# Outside RV64IM (not constrained here): none

include RV32I
include RV32M
include RV64I
include RV64M

forbid ADDW
forbid AND
forbid ANDI
forbid BGEU
forbid DIV
forbid DIVU
forbid DIVUW
forbid DIVW
forbid EBREAK
forbid ECALL
forbid FENCE
forbid LB
forbid LH
forbid LHU
forbid LWU
forbid MULH
forbid MULHSU
forbid MULHU
forbid MULW
forbid OR
forbid ORI
forbid REM
forbid REMU
forbid REMUW
forbid REMW
forbid SH
forbid SLL
forbid SLLIW
forbid SLLW
forbid SLT
forbid SLTIU
forbid SRA
forbid SRAI
forbid SRAIW
forbid SRAW
forbid SRL
forbid SRLIW
forbid SRLW
forbid SUB
forbid SUBW
