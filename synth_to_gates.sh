#!/bin/bash
# Convert RTLIL to gate-level netlist using open source PDK
#
# Usage: ./synth_to_gates.sh <input.il> [output.v]

set -e

if [ "$#" -lt 1 ] || [ "$1" = "-h" ] || [ "$1" = "--help" ]; then
    echo "Usage: $0 <input.il> [output.v]"
    echo ""
    echo "Convert RTLIL design to gate-level Verilog netlist using Skywater PDK"
    echo ""
    echo "Arguments:"
    echo "  input.il    RTLIL file from synth_ibex_with_constraints.sh"
    echo "  output.v    Output gate-level Verilog (default: <input>_gates.v)"
    echo ""
    echo "Environment Variables:"
    echo "  SKYWATER_PDK    Path to Skywater PDK (default: /opt/pdk/skywater-pdk)"
    echo ""
    echo "Examples:"
    echo "  $0 output/ibex_optimized.il"
    echo "  $0 output/ibex_optimized.il output/ibex_gates.v"
    echo "  SKYWATER_PDK=/custom/path $0 output/ibex_optimized.il"
    exit 0
fi

INPUT_IL="$1"

if [ ! -f "$INPUT_IL" ]; then
    echo "ERROR: Input file '$INPUT_IL' not found"
    exit 1
fi

# Default output name
if [ -z "$2" ]; then
    OUTPUT_V="${INPUT_IL%.il}_gates.v"
else
    OUTPUT_V="$2"
fi

# Skywater PDK configuration
SKYWATER_PDK="${SKYWATER_PDK:-/opt/pdk/skywater-pdk}"

# Try to find the liberty file in common locations
SKY130_LIB=""
if [ -f "$SKYWATER_PDK/libraries/sky130_fd_sc_hd/latest/timing/sky130_fd_sc_hd__tt_025C_1v80.lib" ]; then
    SKY130_LIB="$SKYWATER_PDK/libraries/sky130_fd_sc_hd/latest/timing/sky130_fd_sc_hd__tt_025C_1v80.lib"
fi

# Check if Skywater PDK is available
if [ -n "$SKY130_LIB" ]; then
    USE_SKYWATER=true
    LIBERTY_FILE="$SKY130_LIB"
    PDK_NAME="Skywater SKY130 (sky130_fd_sc_hd, tt corner)"
else
    USE_SKYWATER=false
    LIBERTY_FILE="+/ecp5/cells_sim.v"
    PDK_NAME="Generic cells"
    echo "WARNING: Skywater PDK not found at $SKYWATER_PDK"
    echo "         Falling back to generic library"
    echo ""
fi

echo "=========================================="
echo "Gate-Level Synthesis"
echo "=========================================="
echo "Input RTLIL:  $INPUT_IL"
echo "Output Gates: $OUTPUT_V"
echo "PDK:          $PDK_NAME"
echo ""

# Create Yosys script for gate-level synthesis
SCRIPT="${INPUT_IL%.il}_gate_synth.ys"

cat > "$SCRIPT" << EOF
# Gate-level synthesis script
# Converts RTLIL to gate-level netlist using $PDK_NAME

# Read the RTLIL design
read_rtlil $INPUT_IL

# Remove any leftover formal cells (assertions/assumptions already used in ABC optimization)
chformal -remove

# Full synthesis to gate level
synth -top ibex_core

# Map to standard cells
dfflibmap -liberty $LIBERTY_FILE
abc -liberty $LIBERTY_FILE

# Cleanup
opt_clean

# Write gate-level Verilog netlist
write_verilog -noattr -noexpr -nohex $OUTPUT_V

# Print statistics
stat -liberty $LIBERTY_FILE
EOF

echo "Running gate-level synthesis..."
yosys -s "$SCRIPT"

if [ $? -eq 0 ]; then
    echo ""
    echo "=========================================="
    echo "SUCCESS!"
    echo "=========================================="
    echo "Generated:"
    echo "  - $OUTPUT_V (gate-level Verilog)"
    echo "  - $SCRIPT (synthesis script)"
    echo ""
    echo "PDK used: $PDK_NAME"
    if [ "$USE_SKYWATER" = true ]; then
        echo "Standard cell library: sky130_fd_sc_hd (high density)"
        echo "Corner: tt_025C_1v80 (typical, 25°C, 1.8V)"
    fi
else
    echo "ERROR: Gate-level synthesis failed"
    exit 1
fi
