version 2

# Embench ud, compiled for RV64IM (see make_workload_crisp.py).
# Uses 29 RV64IM instructions: ADD ADDI ADDIW ADDW AUIPC BEQ BGE BLT BLTU BNE DIV JAL JALR LBU LD LUI LW MUL OR SB SD SLLI SLTIU SLTU SRLI SUB SUBW SW XORI
# Outside RV64IM (not constrained here): none

include RV32I
include RV32M
include RV64I
include RV64M

forbid AND
forbid ANDI
forbid BGEU
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
forbid REMUW
forbid REMW
forbid SH
forbid SLL
forbid SLLIW
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
forbid XOR
