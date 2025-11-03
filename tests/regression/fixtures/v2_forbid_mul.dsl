# V2 with forbid - RV32I without multiplication
# Tests v2 forbid functionality

version 2

include RV32I
include RV32M

forbid MUL
forbid MULH
forbid MULHSU
forbid MULHU
forbid DIV
forbid DIVU
forbid REM
forbid REMU
