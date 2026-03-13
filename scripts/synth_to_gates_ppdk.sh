#!/bin/bash
# Convert optimized AIGER to gate-level netlist using PPDK Standard Library
#
# Usage: ./synth_to_gates_ppdk.sh <input_base> [output.v] [clk_name] [module_name]
#        where <input_base>_post_abc.aig is the optimized AIGER from external ABC

set -e

if [ "$#" -lt 1 ] || [ "$1" = "-h" ] || [ "$1" = "--help" ]; then
    echo "Usage: $0 <input_base> [output.v] [clk_name] [module_name]"
    echo ""
    echo "Convert ABC-optimized AIGER to gate-level Verilog using PPDK Standard Library"
    echo ""
    echo "Arguments:"
    echo "  input_base   Base path (e.g., output/ibex_optimized)"
    echo "               Will read <input_base>_post_abc.aig"
    echo "  output.v     Output gate-level Verilog (default: <input_base>_gates.v)"
    echo "  clk_name     Clock signal name in AIGER (default: clk_i)"
    echo "  module_name  Top module name for timing analysis (default: auto-detect)"
    echo ""
    echo "Environment Variables:"
    echo "  LIBERTY_FILE    Override path to liberty file"
    echo "  CLK_NAME        Clock signal name (overridden by clk_name argument)"
    echo "  MODULE_NAME     Top module name (overridden by module_name argument)"
    echo ""
    echo "Examples:"
    echo "  $0 output/ibex_optimized"
    echo "  $0 output/ibex_optimized output/ibex_gates.v clk_i"
    echo "  $0 output/ibex_optimized output/ibex_gates.v clk_i ibex_core_with_rf"
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

# Clock name: priority is argument > env var > default
if [ -n "$3" ]; then
    CLK_NAME="$3"
elif [ -n "$CLK_NAME" ]; then
    CLK_NAME="$CLK_NAME"
else
    CLK_NAME="clk_i"
fi

# Module name: priority is argument > env var > auto-detect
if [ -n "$4" ]; then
    MODULE_NAME="$4"
elif [ -n "$MODULE_NAME" ]; then
    MODULE_NAME="$MODULE_NAME"
else
    MODULE_NAME=""  # Will be auto-detected from Verilog
fi

# PPDK Liberty file configuration
# Priority: LIBERTY_FILE env var > project-root PPDK lib
SCRIPT_DIR_GATES="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
PROJECT_ROOT="$(cd "$SCRIPT_DIR_GATES/../../.." && pwd)"
PPDK_LIB="$PROJECT_ROOT/PPDK_Standard_Library_1.0V_25C_TYP_X1.lib"

if [ -n "$LIBERTY_FILE" ] && [ -f "$LIBERTY_FILE" ]; then
    PDK_NAME="Custom liberty: $(basename $LIBERTY_FILE)"
elif [ -f "$PPDK_LIB" ]; then
    LIBERTY_FILE="$PPDK_LIB"
    PDK_NAME="PPDK Standard Library (1.0V, 25C, TYP)"
else
    echo "ERROR: PPDK liberty file not found at $PPDK_LIB"
    echo "       Place PPDK_Standard_Library_1.0V_25C_TYP_X1.lib in project root"
    echo "       or set LIBERTY_FILE env var"
    exit 1
fi

echo "=========================================="
echo "Gate-Level Synthesis (PPDK)"
echo "=========================================="
echo "Input AIGER:  $INPUT_AIG"
echo "Output Gates: $OUTPUT_V"
echo "Clock Name:   $CLK_NAME"
echo "Liberty:      $LIBERTY_FILE"
echo "PDK:          $PDK_NAME"
echo ""

# Create Yosys script for gate-level synthesis
SCRIPT="${INPUT_BASE}_gate_synth.ys"

# Determine clean top module name for output Verilog
# Use MODULE_NAME if provided, otherwise derive from input base
if [ -n "$MODULE_NAME" ]; then
    TOP_MODULE="$MODULE_NAME"
else
    # Extract basename and create clean module name
    TOP_MODULE=$(basename "$INPUT_BASE" | sed 's/[^a-zA-Z0-9_]/_/g')
fi

# Create a custom genlib for ABC from PPDK cells.
# ABC requires a BUF gate for its mapper to work, but PPDK has none.
# We define BUF as 2x INVX1 area. Delays use representative values from liberty.
PPDK_GENLIB="${INPUT_BASE}_ppdk.genlib"
cat > "$PPDK_GENLIB" << 'GENEOF'
GATE ZERO    0 Y=CONST0;
GATE ONE     0 Y=CONST1;
GATE BUF   456840 Y=A;               PIN * NONINV 1 999 1 0 1 0
GATE INVX1 228420 Y=!A;              PIN * INV    1 999 1 0 1 0
GATE NAND2X1 247860 Y=!(A*B);        PIN * INV    1 999 1 0 1 0
GATE NOR2X1  399500 Y=!(A+B);        PIN * INV    1 999 1 0 1 0
GATE AND2X1  433500 Y=A*B;           PIN * NONINV 1 999 1 0 1 0
GATE OR2X1   563530 Y=A+B;           PIN * NONINV 1 999 1 0 1 0
GATE XOR2X1  1042800 Y=(A*!B)+(!A*B);   PIN * UNKNOWN 1 999 1 0 1 0
GATE XNOR2X1 1347557 Y=(A*B)+(!A*!B);  PIN * UNKNOWN 1 999 1 0 1 0
GENEOF

cat > "$SCRIPT" << EOF
# Gate-level synthesis script
# Converts ABC-optimized AIGER to gate-level netlist using $PDK_NAME

# Read the optimized AIGER design from external ABC
# This already has sequential optimization (scorr) applied
# CRITICAL: Use -clk_name to convert latches to clocked \$_DFF_P_ cells
read_aiger -clk_name $CLK_NAME $INPUT_AIG

# Standard synthesis flow for AIGER to gate-level
flatten
opt
memory
opt_clean
fsm
opt
techmap
opt

# PPDK only has DFFNRX1 (pos-edge DFF with active-low async reset) as a true DFF.
# DFFX1 is declared as a latch in this library, so Yosys won't use it for DFFs.
# Convert all \$_DFF_P_ cells to \$_DFF_PN0_ with tied-high reset (inactive).
dfflegalize -cell \$_DFF_PN0_ 0

# Map flip-flops to PPDK DFF cells (DFFNRX1)
dfflibmap -liberty $LIBERTY_FILE

# Map combinational logic using custom genlib (includes BUF gate that PPDK lacks)
abc -genlib $PPDK_GENLIB
opt_clean

# Rename module to clean name (Yosys uses AIGER path as module name)
rename -top $TOP_MODULE

# Write gate-level Verilog netlist
write_verilog -noattr -noexpr -nohex $OUTPUT_V

# Print statistics (with all cell types)
stat

# Print statistics with liberty
stat -liberty $LIBERTY_FILE
EOF

GATES_LOG="${INPUT_BASE}_gates.log"

echo "Running gate-level synthesis..."
yosys -s "$SCRIPT" 2>&1 | tee "$GATES_LOG"

if [ ${PIPESTATUS[0]} -eq 0 ]; then
    # Extract chip area from log
    CHIP_AREA=$(grep "Chip area for module" "$GATES_LOG" | tail -1 | awk '{print $NF}')

    # Extract sequential area breakdown from Yosys output
    DFF_AREA=$(grep "of which used for sequential elements:" "$GATES_LOG" | tail -1 | awk '{print $7}')

    # Calculate combinational area = total - sequential
    if [ -n "$CHIP_AREA" ] && [ -n "$DFF_AREA" ]; then
        CHIP_AREA_COMB=$(python3 -c "print(f'{float(${CHIP_AREA:-0}) - float(${DFF_AREA:-0}):.2f}')" 2>/dev/null || echo "$CHIP_AREA")
    else
        CHIP_AREA_COMB="$CHIP_AREA"
        DFF_AREA="0"
    fi

    # Extract flip-flop count for reporting
    DFF_COUNT=$(grep -E "Number of cells:" "$GATES_LOG" | tail -1 | awk '{print $NF}')

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
    echo "Liberty:  $LIBERTY_FILE"
    if [ -n "$CHIP_AREA_COMB" ]; then
        echo "Combinational area: $CHIP_AREA_COMB µm²"
    fi
    if [ -n "$DFF_AREA" ] && [ "$DFF_AREA" != "0" ]; then
        echo "Sequential area: $DFF_AREA µm²"
    fi
    if [ -n "$CHIP_AREA" ]; then
        echo "Total chip area: $CHIP_AREA µm² (comb $CHIP_AREA_COMB + seq ${DFF_AREA:-0})"
        # Save total area to file for comparison scripts
        echo "$CHIP_AREA" > "${INPUT_BASE}_total_area.txt"
    fi

    # Post-process gate-level Verilog to fix PPDK pin names
    # Genlib uses pins A, B, Y for 2-input gates but PPDK liberty uses A1, A2, Y
    # Also replace BUF cells (not in PPDK) with two back-to-back INVX1 cells
    echo ""
    echo "Post-processing gate-level Verilog for PPDK pin compatibility..."
    python3 - "$OUTPUT_V" << 'PYEOF'
import sys
import re

verilog_file = sys.argv[1]

TWO_INPUT_GATES = {'NAND2X1', 'NOR2X1', 'AND2X1', 'OR2X1', 'XOR2X1', 'XNOR2X1'}

with open(verilog_file, 'r') as f:
    lines = f.readlines()

output_lines = []
in_two_input = False
in_buf = False
buf_input = None
buf_output = None
buf_name = None

i = 0
while i < len(lines):
    line = lines[i]
    stripped = line.strip()

    # Get first word to detect cell type
    words = stripped.split()
    first_word = words[0] if words else ''

    if first_word in TWO_INPUT_GATES:
        in_two_input = True
        in_buf = False
    elif first_word == 'BUF':
        in_buf = True
        in_two_input = False
        # Extract instance name
        buf_name = words[1].rstrip(' (') if len(words) > 1 else '_buf_'
        buf_input = None
        buf_output = None
        i += 1
        continue
    elif first_word in ('INVX1', 'DFFNRX1', 'module', 'input', 'output', 'wire',
                         'assign', 'endmodule'):
        in_two_input = False
        in_buf = False

    if in_buf:
        # Parse BUF pin connections
        m_a = re.search(r'\.A\((.+?)\)', stripped)
        m_y = re.search(r'\.Y\((.+?)\)', stripped)
        if m_a:
            buf_input = m_a.group(1)
        if m_y:
            buf_output = m_y.group(1)

        if stripped == ');':
            # Replace BUF with two INVX1 instances
            mid_wire = f'{buf_name}_mid_'
            output_lines.append(f'  wire {mid_wire};\n')
            output_lines.append(f'  INVX1 {buf_name}_a_ (\n')
            output_lines.append(f'    .A({buf_input}),\n')
            output_lines.append(f'    .Y({mid_wire})\n')
            output_lines.append(f'  );\n')
            output_lines.append(f'  INVX1 {buf_name}_b_ (\n')
            output_lines.append(f'    .A({mid_wire}),\n')
            output_lines.append(f'    .Y({buf_output})\n')
            output_lines.append(f'  );\n')
            in_buf = False
        i += 1
        continue

    if in_two_input:
        line = line.replace('.A(', '.A1(')
        line = line.replace('.B(', '.A2(')
        if stripped == ');':
            in_two_input = False

    output_lines.append(line)
    i += 1

with open(verilog_file, 'w') as f:
    f.writelines(output_lines)

# Count changes
buf_count = sum(1 for l in output_lines if '_mid_' in l and 'wire' in l)
a1_count = sum(1 for l in output_lines if '.A1(' in l)
print(f"  Fixed {a1_count} two-input gate pin names (A->A1, B->A2)")
print(f"  Replaced {buf_count} BUF cells with INVX1 pairs")
PYEOF

    if [ $? -ne 0 ]; then
        echo "WARNING: Post-processing failed, timing analysis may be inaccurate"
    fi

    # Run timing analysis if OpenSTA is available
    echo ""
    TIMING_SCRIPT="$(dirname "$0")/analyze_timing_ppdk.sh"
    if [ -x "$TIMING_SCRIPT" ] && command -v sta &> /dev/null; then
        echo "Running static timing analysis..."
        "$TIMING_SCRIPT" "$OUTPUT_V" "$CLK_NAME" 10.0 "$MODULE_NAME" "$INPUT_BASE"
    else
        echo "Static timing analysis skipped (OpenSTA not installed or analyze_timing_ppdk.sh not found)"
    fi
else
    echo "ERROR: Gate-level synthesis failed"
    exit 1
fi
