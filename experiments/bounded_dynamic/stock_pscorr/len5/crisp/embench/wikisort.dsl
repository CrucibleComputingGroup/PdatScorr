version 2

# Embench wikisort, compiled for RV64IM (see make_workload_crisp.py).
# Uses 37 RV64IM instructions: ADD ADDI ADDIW ADDW AND ANDI AUIPC BEQ BGE BLT BLTU BNE DIV JAL JALR LBU LD LUI LW LWU MUL OR REM SB SD SLLI SLT SLTIU SLTU SRAI SRAIW SRLI SRLIW SUB SUBW SW XORI
# Outside RV64IM (not constrained here): none

include RV32I
include RV32M
include RV64I
include RV64M

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
forbid MULH
forbid MULHSU
forbid MULHU
forbid MULW
forbid ORI
forbid REMU
forbid REMUW
forbid REMW
forbid SH
forbid SLL
forbid SLLIW
forbid SLLW
forbid SLTI
forbid SRA
forbid SRAW
forbid SRL
forbid SRLW
forbid XOR
