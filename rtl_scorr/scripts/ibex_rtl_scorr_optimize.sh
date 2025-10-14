#!/bin/bash
# RTL-Scorr Optimization on Ibex

echo "RTL-Scorr on Ibex - this will take 5-10 minutes..."
synlig -s output/ibex_rtl_optimize_test.ys 2>&1 | tee output/ibex_final.log

echo ""
echo "Results:"
grep "Chip area" output/ibex_final.log | tail -1
grep "Number of cells:" output/ibex_final.log | tail -1

echo ""
echo "Compare with ABC: 34,024 µm², 6,839 cells"
