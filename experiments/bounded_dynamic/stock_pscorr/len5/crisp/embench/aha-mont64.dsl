version 2

# Embench aha-mont64, compiled for RV64IM (see make_workload_crisp.py).
# Uses 27 RV64IM instructions: ADD ADDI ADDIW AND ANDI AUIPC BEQ BGE BLTU BNE JALR LBU LD LUI MUL MULHU OR SB SD SLLI SLTIU SLTU SRAI SRLI SUB XOR XORI
# Outside RV64IM (not constrained here): none

include RV32I
include RV32M
include RV64I
include RV64M

forbid ADDW
forbid BGEU
forbid BLT
forbid DIV
forbid DIVU
forbid DIVUW
forbid DIVW
forbid EBREAK
forbid ECALL
forbid FENCE
forbid JAL
forbid LB
forbid LH
forbid LHU
forbid LW
forbid LWU
forbid MULH
forbid MULHSU
forbid MULW
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
forbid SLTI
forbid SRA
forbid SRAIW
forbid SRAW
forbid SRL
forbid SRLIW
forbid SRLW
forbid SUBW
forbid SW
