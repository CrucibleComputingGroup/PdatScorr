version 2

# Embench huffbench, compiled for RV64IM (see make_workload_crisp.py).
# Uses 36 RV64IM instructions: ADD ADDI ADDIW ADDW AND ANDI AUIPC BEQ BGE BGEU BLT BLTU BNE JAL JALR LBU LD LUI LW MUL OR ORI SB SD SLLI SLLIW SLLW SLTIU SLTU SRAIW SRLI SRLIW SUB SUBW SW XORI
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
forbid LHU
forbid LWU
forbid MULH
forbid MULHSU
forbid MULHU
forbid MULW
forbid REM
forbid REMU
forbid REMUW
forbid REMW
forbid SH
forbid SLL
forbid SLT
forbid SLTI
forbid SRA
forbid SRAI
forbid SRAW
forbid SRL
forbid SRLW
forbid XOR
