# RV32I only - remove multiply/divide
# Should reduce MDU logic in SERV

version 2

include RV32I
# Explicitly forbid M extension
forbid RV32M
