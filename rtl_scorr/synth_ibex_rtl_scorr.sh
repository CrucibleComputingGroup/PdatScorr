#!/bin/bash
# RTL-Scorr synthesis for Ibex (mirrors synth_ibex_with_constraints.sh)
#
# Usage: ./synth_ibex_rtl_scorr.sh <rules.dsl> [output_dir]

set -e

if [ "$#" -lt 1 ]; then
    echo "Usage: $0 <rules.dsl> [output_dir]"
    echo ""
    echo "Example:"
    echo "  $0 ../dsls/example_outlawed.dsl output/"
    exit 1
fi

INPUT_DSL="$1"
OUTPUT_DIR="${2:-output}"

if [ ! -f "$INPUT_DSL" ]; then
    echo "ERROR: DSL file not found: $INPUT_DSL"
    exit 1
fi

mkdir -p "$OUTPUT_DIR"
BASE="$OUTPUT_DIR/ibex_rtl_scorr"

echo "=========================================="
echo "RTL-Scorr: Ibex Synthesis"
echo "=========================================="
echo "Input DSL:    $INPUT_DSL"
echo "Output:       $BASE"
echo ""

# Step 1: Generate constraints (reuse from main project!)
echo "[1/3] Generating constraints..."
pdat-dsl codegen --inline "$INPUT_DSL" "${BASE}_assumptions.sv"

# Step 2: Inject into Ibex
echo "[2/3] Injecting constraints..."
python3 ../scripts/inject_checker.py --assumptions-file "${BASE}_assumptions.sv" \
    ../cores/ibex/rtl/ibex_id_stage.sv "${BASE}_id_stage.sv"

# Step 3: Synthesize with RTL-Scorr
echo "[3/3] Synthesizing with RTL-Scorr..."

cat > ${BASE}_synth.ys << YEOF
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
  ${BASE}_id_stage.sv \\
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
proc
memory
techmap
share -aggressive
opt -full
flatten
delete t:\\\$scopeinfo t:\\\$assume a:\\\$assume
opt

# Gate synthesis
dfflibmap -liberty /opt/pdk/skywater-pdk/libraries/sky130_fd_sc_hd/latest/timing/sky130_fd_sc_hd__tt_025C_1v80.lib
abc -liberty /opt/pdk/skywater-pdk/libraries/sky130_fd_sc_hd/latest/timing/sky130_fd_sc_hd__tt_025C_1v80.lib
opt_clean

stat -liberty /opt/pdk/skywater-pdk/libraries/sky130_fd_sc_hd/latest/timing/sky130_fd_sc_hd__tt_025C_1v80.lib

write_verilog -noattr ${BASE}_gates.v
YEOF

synlig -s ${BASE}_synth.ys 2>&1 | tee ${BASE}.log

echo ""
echo "=========================================="
echo "Results:"
grep "Chip area\|Number of cells:" ${BASE}.log | tail -2
echo ""
echo "ABC baseline: 34,024 µm², 6,839 cells"
