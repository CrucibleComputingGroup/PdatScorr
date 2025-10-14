#!/bin/bash
# RTL-Scorr: Optimize RTL using SMT-based sequential equivalence checking
#
# Input:  RTL with constraints
# Output: Optimized RTL
#
# Usage: ./rtl_scorr.sh <rtl_with_constraints.sv> <module_name> <output.v>

set -e

if [ "$#" -ne 3 ]; then
    echo "Usage: $0 <rtl_file> <module_name> <output_file>"
    echo ""
    echo "Example:"
    echo "  $0 ../output/test_F2/ibex_optimized_id_stage.sv ibex_id_stage output/ibex_optimized.v"
    exit 1
fi

INPUT_RTL="$1"
MODULE="$2"
OUTPUT_RTL="$3"

echo "RTL-Scorr: $MODULE"
echo "  Input:  $INPUT_RTL"
echo "  Output: $OUTPUT_RTL"
echo ""

# Full RTL-Scorr flow
cat > output/rtl_scorr_temp.ys << YEOF
# Complete RTL-Scorr flow

read_systemverilog \\
  -I../cores/ibex/rtl \\
  -I../cores/ibex/shared/rtl \\
  -I../cores/ibex/vendor/lowrisc_ip/ip/prim/rtl \\
  -I../cores/ibex/vendor/lowrisc_ip/dv/sv/dv_utils \\
  -DYOSYS=1 -DSYNTHESIS=1 \\
  ../cores/ibex/rtl/ibex_pkg.sv \\
  ../cores/ibex/rtl/ibex_decoder.sv \\
  ../cores/ibex/rtl/ibex_controller.sv \\
  $INPUT_RTL

hierarchy -check -top $MODULE

# Optimize
proc
memory
techmap
share -aggressive
opt -full

# Apply SMT-proven equivalences here
# TODO: For each proven equivalence (sig_a, sig_b):
#   connect -set sig_a sig_b

opt_clean

write_verilog -noattr $OUTPUT_RTL
YEOF

echo "Running RTL-Scorr..."
synlig -s output/rtl_scorr_temp.ys 2>&1 | tail -20

if [ -f "$OUTPUT_RTL" ]; then
    echo ""
    echo "✓ Optimized RTL: $OUTPUT_RTL"
else
    echo "ERROR: Optimization failed"
    exit 1
fi
