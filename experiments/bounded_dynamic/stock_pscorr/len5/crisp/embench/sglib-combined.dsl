version 2

# Embench sglib-combined, compiled for RV64IM (see make_workload_crisp.py).
# Uses 35 RV64IM instructions: ADD ADDI ADDIW ADDW AUIPC BEQ BGE BGEU BLT BLTU BNE EBREAK JAL JALR LBU LD LH LUI LW MUL REMUW REMW SB SD SH SLLI SLLIW SLTIU SLTU SRAIW SRLI SUB SUBW SW XORI
# Outside RV64IM (not constrained here): none

include RV32I
include RV32M
include RV64I
include RV64M

forbid AND
forbid ANDI
forbid DIV
forbid DIVU
forbid DIVUW
forbid DIVW
forbid ECALL
forbid FENCE
forbid LB
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
forbid SLL
forbid SLLW
forbid SLT
forbid SLTI
forbid SRA
forbid SRAI
forbid SRAW
forbid SRL
forbid SRLIW
forbid SRLW
forbid XOR
