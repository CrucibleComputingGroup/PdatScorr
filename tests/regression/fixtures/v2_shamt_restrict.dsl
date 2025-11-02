# V2 with shamt field - Restrict shift amounts using 5-bit patterns
# Tests new shamt field and bit pattern constraints

version 2

include RV32I

# Remove all shifts
forbid SLLI
forbid SRLI
forbid SRAI

# Add back only shifts with amount 0-3
include SLLI {shamt = 5'b00000}
include SLLI {shamt = 5'b00001}
include SLLI {shamt = 5'b00010}
include SLLI {shamt = 5'b00011}

include SRLI {shamt = 5'b00000}
include SRLI {shamt = 5'b00001}
include SRLI {shamt = 5'b00010}
include SRLI {shamt = 5'b00011}

include SRAI {shamt = 5'b00000}
include SRAI {shamt = 5'b00001}
include SRAI {shamt = 5'b00010}
include SRAI {shamt = 5'b00011}
