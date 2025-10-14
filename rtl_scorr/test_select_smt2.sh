#!/bin/bash
# Experiment to understand how select and write_smt2 work together

set -e

echo "================================================================================"
echo "Testing Yosys select with write_smt2"
echo "================================================================================"
echo ""

# Test 1: Simple design with cone extraction
echo "Test 1: Simple mux - select result cone and write SMT2"
echo "----------------------------------------------------------------------"

cat > output/test_select_1.ys << 'EOF'
# Load simple_mux
read_systemverilog -DYOSYS=1 examples/simple_mux.v
hierarchy -check -top simple_mux

# Prepare
proc
async2sync
dffunmap
flatten

# Show all wires
log "=== All wires in design ==="
select -list w:*

# Select cone for 'result' wire
log "=== Selecting cone for result ==="
select w:result %ci*
log "Selected:"
select -list

# Write SMT2 with selection active
write_smt2 output/test_select_cone.smt2

# Write SMT2 with everything (clear selection first)
select -clear
write_smt2 output/test_select_all.smt2

log "=== Files written ==="
EOF

synlig -s output/test_select_1.ys > output/test_select_1.log 2>&1

echo "Results:"
wc -l output/test_select_cone.smt2 output/test_select_all.smt2
echo ""
echo "If cone SMT2 == all SMT2, then write_smt2 ignores selection"
echo "If cone SMT2 < all SMT2, then write_smt2 respects selection"
echo ""

# Test 2: Try with different selection strategies
echo "Test 2: Try selecting specific cells/wires before write_smt2"
echo "----------------------------------------------------------------------"

cat > output/test_select_2.ys << 'EOF'
# Load simple design
read_systemverilog -DYOSYS=1 examples/simple_mux.v
hierarchy -check -top simple_mux
proc
async2sync
dffunmap
flatten

# Try selecting just specific wires
select w:result w:data_a w:enable
log "Selected wires:"
select -list

# Write SMT2
write_smt2 output/test_select_specific.smt2

# Compare to full
select -clear
write_smt2 output/test_select_full2.smt2
EOF

synlig -s output/test_select_2.ys > output/test_select_2.log 2>&1

echo "Results:"
wc -l output/test_select_specific.smt2 output/test_select_full2.smt2
echo ""

# Test 3: Check if there's a flag for write_smt2 to respect selection
echo "Test 3: Check write_smt2 help for selection-related options"
echo "----------------------------------------------------------------------"
synlig -p "help write_smt2" 2>&1 | grep -i "select\|chosen\|current" | head -10

echo ""
echo "Test 3: Try using [selection] argument syntax"
echo "----------------------------------------------------------------------"

cat > output/test_select_3.ys << 'EOF'
# Load design
read_systemverilog -DYOSYS=1 examples/simple_mux.v
hierarchy -check -top simple_mux
proc
async2sync
dffunmap
flatten

# Try using [selection] argument syntax (if it exists)
# Syntax: write_smt2 [options] [filename]
# Maybe we can pass selection as final argument?

# First, try without selection
write_smt2 output/test_no_sel.smt2

# Try with selection in various ways
select w:result
write_smt2 output/test_with_sel.smt2

# Try the % operator to save/restore
select w:result %ci*
select -set mycone %
write_smt2 output/test_named_sel.smt2
EOF

synlig -s output/test_select_3.ys > output/test_select_3.log 2>&1

echo "Results:"
wc -l output/test_no_sel.smt2 output/test_with_sel.smt2 output/test_named_sel.smt2 2>&1

echo ""
echo "================================================================================"
echo "Summary of Experiments"
echo "================================================================================"
echo "Check the line counts above to see if selection affects write_smt2 output"
