version 2

# Embench nettle-sha256, compiled for RV64IM (see make_workload_crisp.py).
# Uses 33 RV64IM instructions: ADD ADDI ADDIW ADDW AND ANDI AUIPC BEQ BGE BGEU BLTU BNE JAL JALR LBU LD LHU LUI LW MUL OR SB SD SLLI SLLIW SLTU SRLI SRLIW SUB SUBW SW XOR XORI
# Outside RV64IM (not constrained here): none

include RV32I
include RV32M
include RV64I
include RV64M

forbid BLT
forbid DIV
forbid DIVU
forbid DIVUW
forbid DIVW
forbid EBREAK
forbid ECALL
forbid FENCE
forbid LB
forbid LH
forbid LWU
forbid MULH
forbid MULHSU
forbid MULHU
forbid MULW
forbid ORI
forbid REM
forbid REMU
forbid REMUW
forbid REMW
forbid SH
forbid SLL
forbid SLLW
forbid SLT
forbid SLTI
forbid SLTIU
forbid SRA
forbid SRAI
forbid SRAIW
forbid SRAW
forbid SRL
forbid SRLW
