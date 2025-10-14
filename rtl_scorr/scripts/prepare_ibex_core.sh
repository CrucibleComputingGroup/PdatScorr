#!/bin/bash
# Prepare full Ibex core for RTL-scorr analysis

set -e

if [ "$#" -ne 1 ]; then
    echo "Usage: $0 <ibex_id_stage_with_constraints.sv>"
    echo ""
    echo "Example:"
    echo "  $0 ../output/test_F2/ibex_optimized_id_stage.sv"
    echo ""
    echo "This will analyze the FULL Ibex core with constraints"
    exit 1
fi

ID_STAGE="$1"

if [ ! -f "$ID_STAGE" ]; then
    echo "ERROR: ID stage file not found: $ID_STAGE"
    exit 1
fi

echo "================================================================================"
echo "Preparing FULL Ibex Core for RTL-Scorr Analysis"
echo "================================================================================"
echo ""
echo "Input: $ID_STAGE (with instruction constraints)"
echo "Target: ibex_core (complete processor)"
echo ""

# Create Yosys script for full core
cat > output/prepare_ibex_core.ys << EOF
# Prepare full Ibex core for RTL-level scorr
# This includes: decoder, ALU, multiplier, divider, controller, etc.

read_systemverilog \\
  -I../cores/ibex/rtl \\
  -I../cores/ibex/shared/rtl \\
  -I../cores/ibex/vendor/lowrisc_ip/ip/prim/rtl \\
  -I../cores/ibex/vendor/lowrisc_ip/dv/sv/dv_utils \\
  -DYOSYS=1 -DSYNTHESIS=1 \\
  ../cores/ibex/rtl/ibex_pkg.sv \\
  ../cores/ibex/rtl/ibex_alu.sv \\
  ../cores/ibex/rtl/ibex_compressed_decoder.sv \\
  ../cores/ibex/rtl/ibex_controller.sv \\
  ../cores/ibex/rtl/ibex_decoder.sv \\
  ../cores/ibex/rtl/ibex_ex_block.sv \\
  ../cores/ibex/rtl/ibex_multdiv_fast.sv \\
  ../cores/ibex/rtl/ibex_multdiv_slow.sv \\
  ../cores/ibex/rtl/ibex_counter.sv \\
  ../cores/ibex/rtl/ibex_cs_registers.sv \\
  ../cores/ibex/rtl/ibex_csr.sv \\
  ../cores/ibex/rtl/ibex_dummy_instr.sv \\
  ../cores/ibex/rtl/ibex_fetch_fifo.sv \\
  ../cores/ibex/rtl/ibex_if_stage.sv \\
  ../cores/ibex/rtl/ibex_load_store_unit.sv \\
  ../cores/ibex/rtl/ibex_pmp.sv \\
  ../cores/ibex/rtl/ibex_prefetch_buffer.sv \\
  ../cores/ibex/rtl/ibex_register_file_ff.sv \\
  ../cores/ibex/rtl/ibex_wb_stage.sv \\
  ../cores/ibex/vendor/lowrisc_ip/ip/prim/rtl/prim_assert.sv \\
  ../cores/ibex/rtl/ibex_branch_predict.sv \\
  $ID_STAGE \\
  ../cores/ibex/rtl/ibex_core.sv

# Use ibex_core as top
hierarchy -check -top ibex_core

# Convert to structural netlist (but DON'T flatten - preserve hierarchy!)
proc
opt

# Show statistics
echo "=== Statistics (with hierarchy preserved) ==="
stat

# Save RTLIL
write_rtlil output/ibex_core_prepared.il

# Generate SMT2 (this may be large!)
echo ""
echo "Generating SMT2 model (this may take a minute)..."
async2sync
dffunmap
write_smt2 -wires -stbv -stdt output/ibex_core_smt.smt2
EOF

# Run Synlig
echo "Running Synlig on full Ibex core..."
synlig -s output/prepare_ibex_core.ys 2>&1 | tail -50

if [ -f output/ibex_core_smt.smt2 ]; then
    echo ""
    echo "================================================================================"
    echo "SUCCESS!"
    echo "================================================================================"
    echo "  RTLIL: output/ibex_core_prepared.il"
    echo "  SMT2:  output/ibex_core_smt.smt2"
    echo ""
    ls -lh output/ibex_core_*.smt2 output/ibex_core_*.il
    echo ""
    echo "Next: Check known dead signals (mult_en_dec, div_en_dec, etc.)"
else
    echo "ERROR: SMT2 generation failed"
    exit 1
fi
