version 2

# Embench edn, compiled for RV64IM (see make_workload_crisp.py).
# Uses 35 RV64IM instructions: ADD ADDI ADDIW ADDW AUIPC BEQ BGE BLTU BNE JAL JALR LBU LD LH LHU LUI LW MUL MULW SB SD SH SLLI SLLIW SLTIU SLTU SRA SRAI SRAIW SRAW SRLI SUB SUBW SW XORI
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
forbid LB
forbid LWU
forbid MULH
forbid MULHSU
forbid MULHU
forbid OR
forbid ORI
forbid REM
forbid REMU
forbid REMUW
forbid REMW
forbid SLL
forbid SLLW
forbid SLT
forbid SLTI
forbid SRL
forbid SRLIW
forbid SRLW
forbid XOR
