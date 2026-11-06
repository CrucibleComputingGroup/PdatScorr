version 2

# Embench picojpeg, compiled for RV64IM (see make_workload_crisp.py).
# Uses 44 RV64IM instructions: ADD ADDI ADDIW ADDW AND ANDI AUIPC BEQ BGE BGEU BLT BLTU BNE JAL JALR LB LBU LD LH LHU LUI LW LWU MUL MULW OR SB SD SH SLL SLLI SLLIW SLLW SLTIU SLTU SRAI SRAIW SRAW SRLI SRLIW SUB SUBW SW XORI
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
forbid MULH
forbid MULHSU
forbid MULHU
forbid ORI
forbid REM
forbid REMU
forbid REMUW
forbid REMW
forbid SLT
forbid SLTI
forbid SRA
forbid SRL
forbid SRLW
forbid XOR
