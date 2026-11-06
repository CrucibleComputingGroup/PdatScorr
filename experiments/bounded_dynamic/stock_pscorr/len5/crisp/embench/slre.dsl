version 2

# Embench slre, compiled for RV64IM (see make_workload_crisp.py).
# Uses 35 RV64IM instructions: ADD ADDI ADDIW ADDW AND ANDI AUIPC BEQ BGE BGEU BLT BLTU BNE JAL JALR LBU LD LHU LUI LW MUL OR SB SD SLLI SLLIW SLT SLTIU SLTU SRAI SRLI SUB SUBW SW XORI
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
forbid SLTI
forbid SRA
forbid SRAIW
forbid SRAW
forbid SRL
forbid SRLIW
forbid SRLW
forbid XOR
