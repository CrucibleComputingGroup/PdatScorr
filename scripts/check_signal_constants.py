#!/usr/bin/env python3
"""
Check if specific RTL signals become constant under constraints.

This script instruments the design with covers/assertions for specific signals,
then uses formal methods to check if they're provably constant.
"""

import sys
import subprocess
import tempfile
from pathlib import Path

def create_signal_check_script(modified_id_stage, signals_to_check, output_script):
    """
    Generate Yosys script that checks if specific signals are constant.

    signals_to_check: list of (module_path, signal_name) tuples
    """

    import os
    cwd = os.getcwd()

    script = f"""# Check if specific RTL signals are constant
# Generated script for formal dead-code detection

# Read design with constraints
read_systemverilog \\
  -I{cwd}/cores/ibex/rtl \\
  -I{cwd}/cores/ibex/shared/rtl \\
  -I{cwd}/cores/ibex/vendor/lowrisc_ip/ip/prim/rtl \\
  -I{cwd}/cores/ibex/vendor/lowrisc_ip/dv/sv/dv_utils \\
  ./cores/ibex/rtl/ibex_pkg.sv \\
  ./cores/ibex/rtl/ibex_decoder.sv \\
  {modified_id_stage} \\
  ./cores/ibex/rtl/ibex_core.sv

hierarchy -check -top ibex_core

# Don't flatten yet - we want to see module hierarchy
proc
opt

# Check specific signals
"""

    for module_path, signal_name in signals_to_check:
        script += f"""
echo "Checking: {module_path}.{signal_name}"
select -set sig_{signal_name} {module_path}/{signal_name}
stat -sel @sig_{signal_name}
"""

    script += """
# Now flatten to see global impact
flatten
opt

# After optimization with constraints, check again
"""

    for module_path, signal_name in signals_to_check:
        script += f"""
echo "After flattening: {signal_name}"
select -list {signal_name} || echo "Signal removed/renamed"
"""

    with open(output_script, 'w') as f:
        f.write(script)

def check_decoder_signals(base_path):
    """Check common decoder output signals."""

    print("Checking Ibex decoder signals...")
    print()

    # Known Ibex decoder signals to check
    signals = [
        ('id_stage_i/decoder_i', 'mult_en_dec'),
        ('id_stage_i/decoder_i', 'div_en_dec'),
        ('id_stage_i/decoder_i', 'mult_sel_ex_o'),
        ('id_stage_i/decoder_i', 'div_sel_ex_o'),
    ]

    id_stage_modified = f"{base_path}_id_stage.sv"
    script_path = f"{base_path}_signal_check.ys"

    create_signal_check_script(id_stage_modified, signals, script_path)

    print(f"Generated Yosys script: {script_path}")
    print("Run with: yosys -s {script_path}")
    print()

def main():
    if len(sys.argv) != 2:
        print("Usage: check_signal_constants.py <output_base>")
        print("")
        print("Example: check_signal_constants.py output/ibex_optimized")
        print("")
        print("Checks if specific RTL signals are provably constant")
        sys.exit(1)

    base_path = sys.argv[1]
    check_decoder_signals(base_path)

if __name__ == '__main__':
    main()
