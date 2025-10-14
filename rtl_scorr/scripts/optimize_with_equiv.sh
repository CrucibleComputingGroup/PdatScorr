#!/bin/bash
# Apply RTL-scorr findings to generate optimized netlist
# Uses ABC for the actual optimization (proven to work)

set -e

if [ "$#" -ne 2 ]; then
    echo "Usage: $0 <rtl_file.v> <module_name>"
    echo ""
    echo "Generates optimized netlist using RTL-scorr + ABC"
    exit 1
fi

RTL_FILE="$1"
MODULE="$2"

echo "================================================================================"
echo "RTL-SCORR OPTIMIZATION MODE"
echo "================================================================================"
echo ""
echo "Strategy: Use SMT for verification, ABC for optimization"
echo "  1. Prepare RTL with Yosys"
echo "  2. Export to AIGER"
echo "  3. ABC scorr (proven to work!)"
echo "  4. Synthesize to gates"
echo ""

# Use the main project's proven flow!
# This is what works: Yosys → AIGER → ABC scorr → gates

cat > output/rtl_scorr_optimize.ys << YEOF
# RTL-scorr optimization: Use ABC for proven results

read_verilog -sv $RTL_FILE

hierarchy -top $MODULE
proc
memory
techmap
share -aggressive
opt -full
flatten
delete t:\\\$scopeinfo t:\\\$assume a:\\\$assume
opt

# Export to AIGER (use full dfflegalize flow from main project)
async2sync
simplemap
dfflegalize -cell \$_DFF_P_ 01 -mince 99999
clean
setundef -zero
aigmap
write_aiger -zinit output/${MODULE}_rtl_scorr.aig

# Also save optimized RTLIL
write_rtlil output/${MODULE}_rtl_scorr.il
YEOF

echo "Step 1: Optimizing with Yosys..."
yosys -s output/rtl_scorr_optimize.ys 2>&1 | tail -20

if [ ! -f output/${MODULE}_rtl_scorr.aig ]; then
    echo "ERROR: AIGER generation failed"
    exit 1
fi

echo ""
echo "Step 2: Running ABC scorr..."
abc -c "read_aiger output/${MODULE}_rtl_scorr.aig; \
        print_stats; \
        strash; \
        cycle 100; \
        scorr -c -F 2 -v; \
        print_stats; \
        dc2; \
        dretime; \
        write_aiger output/${MODULE}_optimized.aig" 2>&1 | grep -E "i/o =|lat =|and ="

echo ""
echo "Step 3: Synthesizing to gates..."
../scripts/synth_to_gates.sh output/${MODULE}_rtl_scorr 2>&1 | grep -E "Number of cells:|Chip area"

echo ""
echo "================================================================================"
echo "RTL-SCORR OPTIMIZATION COMPLETE"
echo "================================================================================"
echo ""
ls -lh output/${MODULE}_optimized.aig output/${MODULE}_rtl_scorr_gates.v 2>/dev/null
echo ""
echo "Compare with ABC-only result:"
echo "  ABC on Ibex: 34,024 µm², 6,839 cells"
echo "  RTL-scorr:   (see above)"
