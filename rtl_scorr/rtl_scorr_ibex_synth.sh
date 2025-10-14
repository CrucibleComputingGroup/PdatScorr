#!/bin/bash
# RTL-Scorr synthesis script for Ibex
# Mirrors synth_ibex_with_constraints.sh but does RTL-level optimization
#
# Input: Ibex ID stage with constraints (from main project)
# Output: Optimized RTL or gate netlist

set -e

if [ "$#" -lt 1 ]; then
    echo "Usage: $0 <ibex_id_stage_with_constraints.sv> [output_dir]"
    echo ""
    echo "Example:"
    echo "  $0 ../output/test_F2/ibex_optimized_id_stage.sv output/"
    exit 1
fi

ID_STAGE="$1"
OUTPUT_DIR="${2:-output}"

if [ ! -f "$ID_STAGE" ]; then
    echo "ERROR: ID stage file not found: $ID_STAGE"
    exit 1
fi

mkdir -p "$OUTPUT_DIR"

BASE="$OUTPUT_DIR/ibex_rtl_scorr"

echo "=========================================="
echo "RTL-Scorr: Ibex Optimization"
echo "=========================================="
echo "Input ID stage: $ID_STAGE"
echo "Output base: $BASE"
echo ""

# Generate Yosys synthesis script (like make_synthesis_script.py but for RTL)
cat > ${BASE}_synth.ys << EOF
# RTL-Scorr synthesis script for Ibex
# Reads all Ibex modules and optimizes at RTL level

read_systemverilog \\
  -I../cores/ibex/rtl \\
  -I../cores/ibex/shared/rtl \\
  -I../cores/ibex/vendor/lowrisc_ip/ip/prim/rtl \\
  -I../cores/ibex/vendor/lowrisc_ip/dv/sv/dv_utils \\
  ../cores/ibex/rtl/ibex_pkg.sv \\
  ../cores/ibex/rtl/ibex_alu.sv \\
  ../cores/ibex/rtl/ibex_branch_predict.sv \\
  ../cores/ibex/rtl/ibex_compressed_decoder.sv \\
  ../cores/ibex/rtl/ibex_controller.sv \\
  ../cores/ibex/rtl/ibex_counter.sv \\
  ../cores/ibex/rtl/ibex_cs_registers.sv \\
  ../cores/ibex/rtl/ibex_csr.sv \\
  ../cores/ibex/rtl/ibex_decoder.sv \\
  ../cores/ibex/rtl/ibex_dummy_instr.sv \\
  ../cores/ibex/rtl/ibex_ex_block.sv \\
  ../cores/ibex/rtl/ibex_fetch_fifo.sv \\
  $ID_STAGE \\
  ../cores/ibex/rtl/ibex_if_stage.sv \\
  ../cores/ibex/rtl/ibex_load_store_unit.sv \\
  ../cores/ibex/rtl/ibex_multdiv_fast.sv \\
  ../cores/ibex/rtl/ibex_multdiv_slow.sv \\
  ../cores/ibex/rtl/ibex_pmp.sv \\
  ../cores/ibex/rtl/ibex_prefetch_buffer.sv \\
  ../cores/ibex/rtl/ibex_register_file_ff.sv \\
  ../cores/ibex/rtl/ibex_wb_stage.sv \\
  ../cores/ibex/vendor/lowrisc_ip/ip/prim/rtl/prim_assert.sv \\
  ../cores/ibex/rtl/ibex_core.sv

hierarchy -check -top ibex_core

# RTL-level optimization
proc
memory
techmap
share -aggressive
opt -full

# Remove non-synthesizable
flatten
delete t:\\\$scopeinfo t:\\\$assume a:\\\$assume
opt

# Write optimized RTL (with signal names!)
write_verilog -noattr ${BASE}_optimized.v

# Also synthesize to gates for area comparison
dfflibmap -liberty /opt/pdk/skywater-pdk/libraries/sky130_fd_sc_hd/latest/timing/sky130_fd_sc_hd__tt_025C_1v80.lib
abc -liberty /opt/pdk/skywater-pdk/libraries/sky130_fd_sc_hd/latest/timing/sky130_fd_sc_hd__tt_025C_1v80.lib
opt_clean

stat -liberty /opt/pdk/skywater-pdk/libraries/sky130_fd_sc_hd/latest/timing/sky130_fd_sc_hd__tt_025C_1v80.lib

write_verilog -noattr ${BASE}_gates.v
EOF

echo "Running RTL-Scorr synthesis..."
synlig -s ${BASE}_synth.ys 2>&1 | tee ${BASE}_synth.log

echo ""
echo "=========================================="
echo "RTL-Scorr Complete"
echo "=========================================="
echo "Output files:"
echo "  ${BASE}_optimized.v (optimized RTL)"
echo "  ${BASE}_gates.v (gate netlist)"
echo "  ${BASE}_synth.log (full log)"
echo ""
echo "Results:"
grep "Chip area\|Number of cells:" ${BASE}_synth.log | tail -2
echo ""
echo "Compare with ABC-scorr: 34,024 µm², 6,839 cells"
