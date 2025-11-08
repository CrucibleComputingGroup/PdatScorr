#!/bin/bash
# Convert optimized AIGER to gate-level netlist using open source PDK
#
# Usage: ./synth_to_gates.sh <input_base> [output.v]
#        where <input_base>_post_abc.aig is the optimized AIGER from external ABC

set -e

if [ "$#" -lt 1 ] || [ "$1" = "-h" ] || [ "$1" = "--help" ]; then
    echo "Usage: $0 <input_base> [output.v]"
    echo ""
    echo "Convert ABC-optimized AIGER to gate-level Verilog using Skywater PDK"
    echo ""
    echo "Arguments:"
    echo "  input_base  Base path (e.g., output/ibex_optimized)"
    echo "              Will read <input_base>_post_abc.aig"
    echo "  output.v    Output gate-level Verilog (default: <input_base>_gates.v)"
    echo ""
    echo "Environment Variables:"
    echo "  SKYWATER_PDK    Path to Skywater PDK (default: /opt/pdk/skywater-pdk)"
    echo ""
    echo "Examples:"
    echo "  $0 output/ibex_optimized"
    echo "  $0 output/ibex_optimized output/ibex_gates.v"
    exit 0
fi

INPUT_BASE="$1"
# Remove .il extension if present (for backward compatibility)
INPUT_BASE="${INPUT_BASE%.il}"

INPUT_AIG="${INPUT_BASE}_post_abc.aig"

if [ ! -f "$INPUT_AIG" ]; then
    echo "ERROR: Optimized AIGER file '$INPUT_AIG' not found"
    echo "Make sure external ABC has run to generate it"
    exit 1
fi

# Default output name
if [ -z "$2" ]; then
    OUTPUT_V="${INPUT_BASE}_gates.v"
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
echo "Input AIGER:  $INPUT_AIG"
echo "Output Gates: $OUTPUT_V"
echo "PDK:          $PDK_NAME"
echo ""

# Create Yosys script for gate-level synthesis
SCRIPT="${INPUT_BASE}_gate_synth.ys"

cat > "$SCRIPT" << EOF
# Gate-level synthesis script
# Converts ABC-optimized AIGER to gate-level netlist using $PDK_NAME

# Read the optimized AIGER design from external ABC
# This already has sequential optimization (scorr) applied
read_aiger $INPUT_AIG

# Flatten design for technology mapping
flatten

# Technology mapping to PDK standard cells
dfflibmap -liberty $LIBERTY_FILE

abc -liberty $LIBERTY_FILE -fast

# Cleanup
opt_clean

# Write gate-level Verilog netlist
write_verilog -noattr -noexpr -nohex $OUTPUT_V

# Print statistics (with all cell types)
stat

# Print statistics with liberty (combinational only - skips sequential cells)
stat -liberty $LIBERTY_FILE
EOF

GATES_LOG="${INPUT_BASE}_gates.log"

echo "Running gate-level synthesis..."
yosys -s "$SCRIPT" 2>&1 | tee "$GATES_LOG"

if [ ${PIPESTATUS[0]} -eq 0 ]; then
    # Extract chip area from log (combinational only)
    CHIP_AREA_COMB=$(grep "Chip area" "$GATES_LOG" | tail -1 | awk '{print $NF}')

    # Extract flip-flop count and calculate their area
    # DFF cells: sky130_fd_sc_hd__dfxtp_1 (area ~20 µm²), dfxtp_2, dfxtp_4, etc.
    DFF_COUNT=$(grep -E "sky130_fd_sc_hd__dfx" "$GATES_LOG" | grep -oP 'sky130_fd_sc_hd__dfx\w+\s+\K\d+' | awk '{sum+=$1} END {print sum+0}')

    # Estimate DFF area: assume average ~20 µm² per flip-flop
    DFF_AREA=$(python3 -c "print(f'{$DFF_COUNT * 20.0:.2f}')" 2>/dev/null || echo "0")

    # Total area = combinational + sequential
    CHIP_AREA=$(python3 -c "print(f'{float('${CHIP_AREA_COMB:-0}') + float('${DFF_AREA:-0}'):.2f}')" 2>/dev/null || echo "$CHIP_AREA_COMB")

    echo ""
    echo "=========================================="
    echo "SUCCESS!"
    echo "=========================================="
    echo "Generated:"
    echo "  - $OUTPUT_V (gate-level Verilog)"
    echo "  - $SCRIPT (synthesis script)"
    echo "  - $GATES_LOG (gate synthesis log)"
    echo ""
    echo "PDK used: $PDK_NAME"
    if [ "$USE_SKYWATER" = true ]; then
        echo "Standard cell library: sky130_fd_sc_hd (high density)"
        echo "Corner: tt_025C_1v80 (typical, 25°C, 1.8V)"
        if [ -n "$CHIP_AREA_COMB" ]; then
            echo "Combinational area: $CHIP_AREA_COMB µm²"
        fi
        if [ -n "$DFF_COUNT" ] && [ "$DFF_COUNT" -gt 0 ]; then
            echo "Flip-flops: $DFF_COUNT (estimated area: $DFF_AREA µm²)"
        fi
        if [ -n "$CHIP_AREA" ]; then
            echo "Total chip area: $CHIP_AREA µm² (comb + seq)"
            # Save total area to file for comparison scripts
            echo "$CHIP_AREA" > "${INPUT_BASE}_total_area.txt"
        fi
    fi
else
    echo "ERROR: Gate-level synthesis failed"
    exit 1
fi
