# RV32I without branches (but keep jumps)
# Should simplify branch comparison logic

version 2

include RV32I

# Forbid conditional branches (keep JAL/JALR for function calls)
forbid BEQ
forbid BNE
forbid BLT
forbid BGE
forbid BLTU
forbid BGEU
