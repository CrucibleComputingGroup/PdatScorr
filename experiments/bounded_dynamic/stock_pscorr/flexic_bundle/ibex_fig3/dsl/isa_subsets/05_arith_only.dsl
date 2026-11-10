# Arithmetic and logical operations only
# No loads, stores, branches, or jumps
# Minimal compute-only subset

version 2

# Only include basic arithmetic and logical operations
include ADD
include ADDI
include SUB
include AND
include ANDI
include OR
include ORI
include XOR
include XORI
include SLT
include SLTI
include SLTU
include SLTIU

# Need LUI and AUIPC for immediate loading
include LUI
include AUIPC
