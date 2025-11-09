#!/bin/bash
# Static timing analysis using OpenSTA and Skywater PDK
#
# Usage: ./analyze_timing.sh <gate_level.v> [clock_name] [clock_period_ns] [module_name] [output_base]

set -e

if [ "$#" -lt 1 ] || [ "$1" = "-h" ] || [ "$1" = "--help" ]; then
    echo "Usage: $0 <gate_level.v> [clock_name] [clock_period_ns] [module_name] [output_base]"
    echo ""
    echo "Perform static timing analysis on gate-level Verilog netlist"
    echo ""
    echo "Arguments:"
    echo "  gate_level.v      Gate-level Verilog netlist (must use Skywater cells)"
    echo "  clock_name        Clock signal name (default: clk_i)"
    echo "  clock_period_ns   Target clock period in ns (default: 10.0)"
    echo "  module_name       Top module name (default: auto-detect from Verilog)"
    echo "  output_base       Base path for output files (default: derive from gate_level.v)"
    echo ""
    echo "Environment Variables:"
    echo "  SKYWATER_PDK      Path to Skywater PDK (default: /opt/pdk/skywater-pdk)"
    echo ""
    echo "Requires: OpenSTA (https://github.com/The-OpenROAD-Project/OpenSTA)"
    echo ""
    echo "Examples:"
    echo "  $0 output/ibex_optimized_gates.v"
    echo "  $0 output/ibex_optimized_gates.v clk_i 5.0"
    echo "  $0 output/ibex_optimized_gates.v clk_i 5.0 ibex_core_with_rf"
    echo "  $0 output/ibex_optimized_gates.v clk_i 5.0 ibex_core_with_rf output/ibex_optimized"
    exit 0
fi

GATE_NETLIST="$1"
CLK_NAME="${2:-clk_i}"
CLK_PERIOD="${3:-10.0}"
MODULE_NAME_ARG="$4"
OUTPUT_BASE_ARG="$5"

if [ ! -f "$GATE_NETLIST" ]; then
    echo "ERROR: Gate-level netlist '$GATE_NETLIST' not found"
    exit 1
fi

# Check if OpenSTA is installed
if ! command -v sta &> /dev/null; then
    echo "WARNING: OpenSTA not found in PATH"
    echo "         Skipping timing analysis"
    echo ""
    echo "To install OpenSTA:"
    echo "  1. Visit: https://github.com/The-OpenROAD-Project/OpenSTA"
    echo "  2. Or install OpenROAD (includes OpenSTA): https://github.com/The-OpenROAD-Project/OpenROAD"
    exit 0
fi

# Skywater PDK paths
SKYWATER_PDK="${SKYWATER_PDK:-/opt/pdk/skywater-pdk}"
SKY130_LIB="/opt/pdk/skywater-pdk/libraries/sky130_fd_sc_hd/latest/timing/sky130_fd_sc_hd__tt_025C_1v80.lib"

if [ ! -f "$SKY130_LIB" ]; then
    echo "ERROR: Skywater timing library not found at $SKY130_LIB"
    exit 1
fi

# Determine base path for output files
if [ -n "$OUTPUT_BASE_ARG" ]; then
    # Use provided base path (for consistent metrics location)
    OUTPUT_BASE="$OUTPUT_BASE_ARG"
else
    # Derive from gate netlist path
    OUTPUT_BASE="${GATE_NETLIST%.v}"
fi

SDC_FILE="${OUTPUT_BASE}_timing.sdc"
STA_SCRIPT="${OUTPUT_BASE}_sta.tcl"
STA_REPORT="${OUTPUT_BASE}_timing_report.txt"

echo "=========================================="
echo "Static Timing Analysis"
echo "=========================================="
echo "Netlist:      $GATE_NETLIST"
echo "Clock:        $CLK_NAME @ ${CLK_PERIOD}ns ($(python3 -c "print(f'{1000.0/float(\"$CLK_PERIOD\"):.2f}')") MHz)"
echo "Liberty:      sky130_fd_sc_hd (tt corner, 25°C, 1.8V)"
echo ""

# Create SDC file with timing constraints
cat > "$SDC_FILE" << EOF
# Timing constraints for STA
# Generated for: $(basename "$GATE_NETLIST")
# Clock: $CLK_NAME @ ${CLK_PERIOD}ns

# Define clock
create_clock -name clk -period $CLK_PERIOD [get_ports $CLK_NAME]

# Set input/output delays (assume 20% of clock period)
set input_delay [expr {$CLK_PERIOD * 0.2}]
set output_delay [expr {$CLK_PERIOD * 0.2}]

# Set input delays on all inputs except clock
# OpenSTA doesn't have remove_from_collection, so we set delays on all then override clock to 0
set_input_delay -clock clk \$input_delay [all_inputs]
set_input_delay -clock clk 0.0 [get_ports {$CLK_NAME}]

# Set output delays on all outputs
set_output_delay -clock clk \$output_delay [all_outputs]

# Set load capacitance on outputs (typical 4 gate loads)
set_load 0.05 [all_outputs]
EOF

# Create OpenSTA script
cat > "$STA_SCRIPT" << EOF
# OpenSTA analysis script
# Generated for: $(basename "$GATE_NETLIST")

# Error handling - exit on any error
proc handle_error {msg} {
    puts "ERROR: \$msg"
    exit
}

# Read liberty timing library
if {[catch {read_liberty $SKY130_LIB} err]} {
    handle_error "Failed to read Liberty file: \$err"
}

# Read gate-level netlist
if {[catch {read_verilog $GATE_NETLIST} err]} {
    handle_error "Failed to read Verilog netlist: \$err"
}

# Link design (resolve references)
if {[catch {link_design @TOP_MODULE@} err]} {
    handle_error "Failed to link design: \$err"
}

# Read timing constraints
if {[catch {read_sdc $SDC_FILE} err]} {
    handle_error "Failed to read SDC: \$err"
}

# Run timing analysis
report_checks -path_delay min_max -format full_clock_expanded -fields {slew cap input_pins fanout} -digits 3

# Summary reports
puts ""
puts "=========================================="
puts "TIMING SUMMARY"
puts "=========================================="

# Report worst paths
report_worst_slack -min -digits 3
report_worst_slack -max -digits 3
report_tns -digits 3

puts ""
puts "Critical Path Summary:"
report_checks -path_delay max -format summary -group_path_count 1

puts ""
puts "Hold Path Summary:"
report_checks -path_delay min -format summary -group_path_count 1

# Report clock frequency
set wns [sta::worst_slack -max]
if { \$wns != "INFINITY" && \$wns != "-INFINITY" } {
    set max_freq [expr {1000.0 / ($CLK_PERIOD - \$wns)}]
    puts ""
    puts "Maximum Clock Frequency:"
    puts "  Target: [expr {1000.0 / $CLK_PERIOD}] MHz ($CLK_PERIOD ns period)"
    puts "  Actual: [format "%.2f" \$max_freq] MHz ([format "%.3f" [expr {1000.0 / \$max_freq}]] ns period)"
    puts "  Slack:  [format "%.3f" \$wns] ns"
}

# Exit OpenSTA
exit
EOF

# Auto-detect module name from Verilog file first
# Module names may be escaped identifiers like \path/to/module
DETECTED_MODULE=$(grep -m 1 "^module " "$GATE_NETLIST" | sed 's/module \([^ (]*\).*/\1/')

if [ -z "$DETECTED_MODULE" ]; then
    echo "ERROR: Could not extract module name from $GATE_NETLIST"
    exit 1
fi

# Determine which module name to use
if [ -n "$MODULE_NAME_ARG" ]; then
    # Argument provided - verify it matches or warn user
    if [ "$MODULE_NAME_ARG" = "$DETECTED_MODULE" ]; then
        MODULE_NAME="$MODULE_NAME_ARG"
        echo "Using specified module: $MODULE_NAME (matches Verilog)"
    else
        echo "WARNING: Specified module '$MODULE_NAME_ARG' differs from detected '$DETECTED_MODULE'"
        echo "         Using detected module from Verilog: $DETECTED_MODULE"
        MODULE_NAME="$DETECTED_MODULE"
    fi
else
    MODULE_NAME="$DETECTED_MODULE"
    echo "Auto-detected top module: $MODULE_NAME"
fi
echo ""

# Update script with actual module name (use | as delimiter to handle / in module names)
# Escape backslashes for TCL by doubling them
MODULE_NAME_ESCAPED="${MODULE_NAME//\\/\\\\}"
sed -i "s|@TOP_MODULE@|$MODULE_NAME_ESCAPED|g" "$STA_SCRIPT"

echo "Running OpenSTA..."
sta -no_init -no_splash "$STA_SCRIPT" 2>&1 | tee "$STA_REPORT"

STA_EXIT=${PIPESTATUS[0]}

if [ $STA_EXIT -eq 0 ]; then
    echo ""
    echo "=========================================="
    echo "STA COMPLETE"
    echo "=========================================="
    echo "Generated:"
    echo "  - $STA_REPORT (detailed timing report)"
    echo "  - $SDC_FILE (timing constraints)"
    echo "  - $STA_SCRIPT (OpenSTA script)"
    echo ""

    # Extract key metrics for easy access
    WNS=$(grep "worst slack max" "$STA_REPORT" | tail -1 | awk '{print $NF}')
    TNS=$(grep "tns max" "$STA_REPORT" | tail -1 | awk '{print $NF}')

    if [ -n "$WNS" ]; then
        # Calculate maximum achievable frequency from WNS
        # Max period = target period - WNS (if WNS is negative, circuit is slower than target)
        MAX_FREQ=$(python3 -c "wns=float('$WNS'); period=float('$CLK_PERIOD'); max_period = period - wns; print(f'{1000.0/max_period:.2f}' if max_period > 0 else '0.00')" 2>/dev/null || echo "0.00")

        echo "Key Metrics:"
        echo "  WNS (Worst Negative Slack): $WNS ns"
        if [ -n "$TNS" ]; then
            echo "  TNS (Total Negative Slack): $TNS ns"
        fi
        echo "  Max Frequency: $MAX_FREQ MHz"

        # Save metrics to JSON for automated analysis
        cat > "${OUTPUT_BASE}_timing_metrics.json" << EOJSON
{
  "clock_name": "$CLK_NAME",
  "clock_period_ns": $CLK_PERIOD,
  "target_frequency_mhz": $(python3 -c "print(f'{1000.0/float(\"$CLK_PERIOD\"):.2f}')"),
  "wns_ns": $WNS,
  "tns_ns": $TNS,
  "max_frequency_mhz": $MAX_FREQ,
  "pdk": "sky130_fd_sc_hd",
  "corner": "tt_025C_1v80"
}
EOJSON
        echo "  - ${OUTPUT_BASE}_timing_metrics.json (machine-readable metrics)"
    fi
else
    echo "ERROR: OpenSTA analysis failed"
    exit 1
fi
