#!/bin/bash
# RTL-Scorr on Ibex: Complete flow in one script
# Usage: ./rtl_scorr_ibex.sh

set -e

IBEX_ID_STAGE="../output/test_F2/ibex_optimized_id_stage.sv"

echo "================================================================================"
echo "RTL-SCORR ON IBEX"
echo "================================================================================"
echo ""

# Generate optimized Ibex with Yosys
cat > output/ibex_optimize.ys << 'EOF'
read_systemverilog \
  -I../cores/ibex/rtl \
  -I../cores/ibex/shared/rtl \
  -I../cores/ibex/vendor/lowrisc_ip/ip/prim/rtl \
  -I../cores/ibex/vendor/lowrisc_ip/dv/sv/dv_utils \
  -DYOSYS=1 -DSYNTHESIS=1 \
  ../cores/ibex/rtl/ibex_pkg.sv \
  ../cores/ibex/rtl/ibex_alu.sv \
  ../cores/ibex/rtl/ibex_compressed_decoder.sv \
  ../cores/ibex/rtl/ibex_controller.sv \
  ../cores/ibex/rtl/ibex_decoder.sv \
  ../cores/ibex/rtl/ibex_ex_block.sv \
  ../cores/ibex/rtl/ibex_multdiv_fast.sv \
  ../cores/ibex/rtl/ibex_multdiv_slow.sv \
  ../cores/ibex/rtl/ibex_counter.sv \
  ../cores/ibex/rtl/ibex_cs_registers.sv \
  ../cores/ibex/rtl/ibex_csr.sv \
  ../cores/ibex/rtl/ibex_dummy_instr.sv \
  ../cores/ibex/rtl/ibex_fetch_fifo.sv \
  ../cores/ibex/rtl/ibex_if_stage.sv \
  ../cores/ibex/rtl/ibex_load_store_unit.sv \
  ../cores/ibex/rtl/ibex_pmp.sv \
  ../cores/ibex/rtl/ibex_prefetch_buffer.sv \
  ../cores/ibex/rtl/ibex_register_file_ff.sv \
  ../cores/ibex/rtl/ibex_wb_stage.sv \
  ../cores/ibex/vendor/lowrisc_ip/ip/prim/rtl/prim_assert.sv \
  ../cores/ibex/rtl/ibex_branch_predict.sv \
  ../output/test_F2/ibex_optimized_id_stage.sv \
  ../cores/ibex/rtl/ibex_core.sv

hierarchy -check -top ibex_core
proc
memory
techmap
share -aggressive
opt -full
flatten
delete t:$scopeinfo t:$assume a:$assume
opt

# Synthesize to gates
dfflibmap -liberty /opt/pdk/skywater-pdk/libraries/sky130_fd_sc_hd/latest/timing/sky130_fd_sc_hd__tt_025C_1v80.lib
abc -liberty /opt/pdk/skywater-pdk/libraries/sky130_fd_sc_hd/latest/timing/sky130_fd_sc_hd__tt_025C_1v80.lib
opt_clean

stat -liberty /opt/pdk/skywater-pdk/libraries/sky130_fd_sc_hd/latest/timing/sky130_fd_sc_hd__tt_025C_1v80.lib

write_verilog output/ibex_rtl_scorr_gates.v
EOF

echo "Synthesizing Ibex with RTL-scorr..."
synlig -s output/ibex_optimize.ys 2>&1 | tee output/ibex_rtl_scorr.log

echo ""
echo "================================================================================"
echo "RESULTS"
echo "================================================================================"

grep "Chip area\|Number of cells:" output/ibex_rtl_scorr.log | tail -2

echo ""
echo "Baseline (ABC-scorr): 34,024 µm², 6,839 cells"
echo ""
