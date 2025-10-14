#!/bin/bash
# Measure the impact of optimizations on full Ibex core

set -e

echo "================================================================================"
echo "Measuring Optimization Impact on Full Ibex Core"
echo "================================================================================"
echo ""
echo "This will show:"
echo "  1. Baseline (proc + memory + techmap)"
echo "  2. + Structural hashing (share -aggressive)"
echo "  3. + Full optimization (opt -full)"
echo "  4. SMT2 model sizes"
echo ""

# Test without constraints file first
if [ ! -f ../output/test_F2/ibex_optimized_id_stage.sv ]; then
    echo "ERROR: Need Ibex with constraints:"
    echo "  ../output/test_F2/ibex_optimized_id_stage.sv"
    exit 1
fi

cat > output/measure_opt.ys << 'YOSYS_EOF'
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

tee -q -o output/stats_baseline.txt stat

# Structural hashing
share -aggressive

tee -q -o output/stats_after_share.txt stat

# Full optimization
opt -full

tee -q -o output/stats_after_opt.txt stat
YOSYS_EOF

echo "Running Yosys optimization pipeline..."
synlig -s output/measure_opt.ys 2>&1 > output/measure.log

if [ $? -eq 0 ]; then
    echo ""
    echo "================================================================================"
    echo "RESULTS"
    echo "================================================================================"
    echo ""

    echo "Baseline (proc + memory + techmap):"
    grep "design hierarchy ===" -A 25 output/stats_baseline.txt | grep "Number of cells:" | head -1

    echo ""
    echo "After structural hashing (share -aggressive):"
    grep "design hierarchy ===" -A 25 output/stats_after_share.txt | grep "Number of cells:" | head -1

    echo ""
    echo "After full optimization (opt -full):"
    grep "design hierarchy ===" -A 25 output/stats_after_opt.txt | grep "Number of cells:" | head -1

    echo ""
    echo "================================================================================"
    echo ""
    echo "Next: Apply cone extraction to see further reduction"
else
    echo "ERROR: Optimization failed"
    exit 1
fi
