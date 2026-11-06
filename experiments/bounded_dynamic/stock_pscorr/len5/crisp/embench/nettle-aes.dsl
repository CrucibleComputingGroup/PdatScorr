version 2

# Embench nettle-aes, compiled for RV64IM (see make_workload_crisp.py).
# Uses 31 RV64IM instructions: ADD ADDI ADDIW ADDW ANDI AUIPC BEQ BGE BGEU BLTU BNE JAL JALR LBU LD LUI LW MUL OR REMUW SB SD SLLI SLLIW SLTU SRLI SRLIW SUBW SW XOR XORI
# Outside RV64IM (not constrained here): none

include RV32I
include RV32M
include RV64I
include RV64M

forbid AND
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
forbid LHU
forbid LWU
forbid MULH
forbid MULHSU
forbid MULHU
forbid MULW
forbid ORI
forbid REM
forbid REMU
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
forbid SUB
