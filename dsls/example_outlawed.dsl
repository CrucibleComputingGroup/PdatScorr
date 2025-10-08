# Example outlawed instruction specification

# Outlaw all multiply and divide instructions (RV32M extension)
instruction MUL
instruction MULH
instruction MULHSU
instruction MULHU
instruction DIV
instruction DIVU
instruction REM
instruction REMU

# Outlaw specific patterns
# Example: Outlaw ADD when destination is x0 (NOP-like behavior)
instruction ADD { rd = x0 }

# Low-level pattern example
# pattern 0x00000013 mask 0xFFFFFFFF  # ADDI x0, x0, 0 (canonical NOP)
