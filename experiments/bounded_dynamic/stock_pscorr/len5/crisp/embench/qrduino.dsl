version 2

# Embench qrduino, compiled for RV64IM (see make_workload_crisp.py).
# Uses 42 RV64IM instructions: ADD ADDI ADDIW ADDW AND ANDI AUIPC BEQ BGE BGEU BLT BLTU BNE JAL JALR LBU LD LHU LUI LW LWU MUL MULW OR ORI SB SD SH SLLI SLLIW SLTIU SLTU SRAIW SRAW SRLI SRLIW SRLW SUB SUBW SW XOR XORI
# Outside RV64IM (not constrained here): none

include RV32I
include RV32M
include RV64I
include RV64M

forbid DIV
forbid DIVU
forbid DIVUW
forbid DIVW
forbid EBREAK
forbid ECALL
forbid FENCE
forbid LB
forbid LH
forbid MULH
forbid MULHSU
forbid MULHU
forbid REM
forbid REMU
forbid REMUW
forbid REMW
forbid SLL
forbid SLLW
forbid SLT
forbid SLTI
forbid SRA
forbid SRAI
forbid SRL
