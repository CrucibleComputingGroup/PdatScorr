version 2

# Embench matmult-int, compiled for RV64IM (see make_workload_crisp.py).
# Uses 26 RV64IM instructions: ADD ADDI ADDIW ADDW AUIPC BEQ BGE BLTU BNE JALR LBU LD LUI LW MUL REMW SB SD SLLI SLLIW SLTIU SLTU SRLI SUB SW XORI
# Outside RV64IM (not constrained here): none

include RV32I
include RV32M
include RV64I
include RV64M

forbid AND
forbid ANDI
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
forbid SH
forbid SLL
forbid SLLW
forbid SLT
forbid SLTI
forbid SRA
forbid SRAI
forbid SRAIW
forbid SRAW
forbid SRL
forbid SRLIW
forbid SRLW
forbid SUBW
forbid XOR
