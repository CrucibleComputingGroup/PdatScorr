# Simple constraint test fixture
# Tests basic instruction constraint functionality

require RV32I
require RV32M

# Apply data type constraints to test constraint generation
instruction MUL { dtype = ~(i8 | i16) }
instruction DIV { dtype = ~(i8 | i16) }
