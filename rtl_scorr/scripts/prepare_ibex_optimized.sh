#!/bin/bash
# Prepare Ibex with structural hashing and cone-of-influence reduction
# This creates a MINIMAL SMT2 model for checking specific signals

set -e

if [ "$#" -ne 2 ]; then
    echo "Usage: $0 <ibex_id_stage.sv> <signals_to_check>"
    echo ""
    echo "Example:"
    echo "  $0 ../output/test_F2/ibex_optimized_id_stage.sv \"mult_en_dec div_en_dec\""
    echo ""
    echo "Generates optimized, minimal SMT2 model for checking specific signals"
    exit 1
fi

ID_STAGE="$1"
SIGNALS="$2"

echo "================================================================================"
echo "Optimized Ibex Preparation: Structural Hashing + Cone Extraction"
echo "================================================================================"
echo ""
echo "Target signals: $SIGNALS"
echo "Strategy:"
echo "  1. Structural hashing (remove duplicate subcircuits)"
echo "  2. Aggressive optimization"
echo "  3. Cone-of-influence extraction (only relevant logic)"
echo "  4. Minimal SMT2 generation"
echo ""

# Create optimized Yosys script
cat > output/prepare_optimized.ys << EOF
# Optimized preparation: structural hashing + cone extraction

read_systemverilog \\
  -I../cores/ibex/rtl \\
  -I../cores/ibex/shared/rtl \\
  -I../cores/ibex/vendor/lowrisc_ip/ip/prim/rtl \\
  -I../cores/ibex/vendor/lowrisc_ip/dv/sv/dv_utils \\
  -DYOSYS=1 -DSYNTHESIS=1 \\
  ../cores/ibex/rtl/ibex_pkg.sv \\
  ../cores/ibex/rtl/ibex_decoder.sv \\
  ../cores/ibex/rtl/ibex_controller.sv \\
  $ID_STAGE

hierarchy -check -top ibex_id_stage

# Convert processes to gates
proc

# === STRUCTURAL HASHING ===
# Find and share common subcircuits (like ABC's strash)
share -aggressive

# === AGGRESSIVE OPTIMIZATION ===
# Constant propagation, dead code elimination
opt -full

# Show stats after optimization
stat

# === CONE-OF-INFLUENCE EXTRACTION ===
# Select target signals and their dependencies
EOF

# Build signal selection list
first_sig=$(echo $SIGNALS | awk '{print $1}')
rest_sigs=$(echo $SIGNALS | awk '{$1=""; print $0}')

# First signal (creates the set)
echo "select -set target w:$first_sig" >> output/prepare_optimized.ys

# Add remaining signals
for sig in $rest_sigs; do
    if [ -n "$sig" ]; then
        echo "select -add @target w:$sig" >> output/prepare_optimized.ys
    fi
done

cat >> output/prepare_optimized.ys << 'EOF'

# Add input cone (all logic that feeds target signals)
# %ci* = cone of influence (all input dependencies)
select -add @target %ci*

# Also need to keep assumptions and constraints
select -add a:$assume*
select -add w:instr_* w:rst_ni w:clk_i

# Show what we're keeping
echo "=== Cone of Influence (signals kept) ==="
ls -selected

# Delete everything else
delete -selected -inverse

# Show reduced stats
echo "=== After Cone Extraction ==="
stat

# Save reduced RTLIL
write_rtlil output/ibex_id_stage_reduced.il

# Generate SMT2 from reduced model
async2sync
dffunmap
write_smt2 -wires -stbv -stdt output/ibex_id_stage_reduced.smt2
EOF

echo "Running optimized preparation..."
synlig -s output/prepare_optimized.ys 2>&1 | tail -100

if [ -f output/ibex_id_stage_reduced.smt2 ]; then
    echo ""
    echo "================================================================================"
    echo "SUCCESS!"
    echo "================================================================================"

    FULL_SIZE=$(wc -l < output/ibex_core_smt.smt2 2>/dev/null || echo "N/A")
    REDUCED_SIZE=$(wc -l < output/ibex_id_stage_reduced.smt2)

    echo "  Full model:    $FULL_SIZE lines"
    echo "  Reduced model: $REDUCED_SIZE lines"

    if [ "$FULL_SIZE" != "N/A" ]; then
        REDUCTION=$((100 - (REDUCED_SIZE * 100 / FULL_SIZE)))
        echo "  Reduction:     ${REDUCTION}%"
    fi

    echo ""
    ls -lh output/ibex_id_stage_reduced.*
    echo ""
    echo "Next: Query this minimal model to check if signals are constant"
else
    echo "ERROR: Optimized SMT2 generation failed"
    exit 1
fi
