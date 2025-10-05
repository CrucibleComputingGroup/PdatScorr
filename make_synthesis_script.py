#!/usr/bin/env python3
"""
Generate a Yosys/Synlig synthesis script for Ibex with instruction checker.
"""

import argparse

def generate_synthesis_script(checker_module: str, id_stage_modified: str, output_aig: str) -> str:
    """Generate the Yosys synthesis script."""

    import os

    # Use absolute paths for include directories to ensure they're found
    cwd = os.getcwd()

    script = f"""# Synlig script to convert ibex core wrapper (with instruction checker) to AIGER format
# Auto-generated synthesis script

# Set include directories (using absolute paths for reliability)
verilog_defaults -add -I{cwd}/cores/ibex/rtl
verilog_defaults -add -I{cwd}/cores/ibex/shared/rtl
verilog_defaults -add -I{cwd}/cores/ibex/vendor/lowrisc_ip/ip/prim/rtl
verilog_defaults -add -I{cwd}/cores/ibex/vendor/lowrisc_ip/dv/sv/dv_utils

# Read all Ibex files together so packages are available to all modules
# This ensures ibex_pkg is visible to all modules that import it
# Include -I flags directly in read command as verilog_defaults may not propagate to Surelog
read_systemverilog \\
  -I{cwd}/cores/ibex/rtl \\
  -I{cwd}/cores/ibex/shared/rtl \\
  -I{cwd}/cores/ibex/vendor/lowrisc_ip/ip/prim/rtl \\
  -I{cwd}/cores/ibex/vendor/lowrisc_ip/dv/sv/dv_utils \\
  ./cores/ibex/rtl/ibex_pkg.sv \\
  ./cores/ibex/rtl/ibex_alu.sv \\
  ./cores/ibex/rtl/ibex_branch_predict.sv \\
  ./cores/ibex/rtl/ibex_compressed_decoder.sv \\
  ./cores/ibex/rtl/ibex_controller.sv \\
  ./cores/ibex/rtl/ibex_counter.sv \\
  ./cores/ibex/rtl/ibex_cs_registers.sv \\
  ./cores/ibex/rtl/ibex_csr.sv \\
  ./cores/ibex/rtl/ibex_decoder.sv \\
  ./cores/ibex/rtl/ibex_dummy_instr.sv \\
  ./cores/ibex/rtl/ibex_ex_block.sv \\
  ./cores/ibex/rtl/ibex_fetch_fifo.sv \\
  ./{id_stage_modified} \\
  ./cores/ibex/rtl/ibex_if_stage.sv \\
  ./cores/ibex/rtl/ibex_load_store_unit.sv \\
  ./cores/ibex/rtl/ibex_multdiv_fast.sv \\
  ./cores/ibex/rtl/ibex_multdiv_slow.sv \\
  ./cores/ibex/rtl/ibex_pmp.sv \\
  ./cores/ibex/rtl/ibex_prefetch_buffer.sv \\
  ./cores/ibex/rtl/ibex_register_file_ff.sv \\
  ./cores/ibex/rtl/ibex_wb_stage.sv \\
  ./cores/ibex/vendor/lowrisc_ip/ip/prim/rtl/prim_assert.sv \\
  ./cores/ibex/rtl/ibex_core.sv \\
  ./{checker_module}

# Prepare the design for synthesis using ibex_core as top
hierarchy -check -top ibex_core

# Synthesis to gate level (WITHOUT running ABC yet)
# We keep the assertions so ABC+scorr can use them together
synth -run coarse
techmap
opt

# Write RTLIL with assertions still present
# Next step: Run ABC with scorr using a separate script that processes assumptions
write_rtlil {output_aig}_pre_abc.il

# Convert assertions to assumptions BEFORE ABC
chformal -assume -lower

# ABC optimization using assumptions as don't-care constraints
# Use dc2 and fraig which respect assumptions for unreachable state optimization
abc -script "+strash; dc2; scorr; fraig"

opt_clean

# Remove formal cells (already used by ABC)
chformal -remove

# Write optimized output (MUL/DIV logic should be removed)
write_rtlil {output_aig}.il
"""
    return script

def main():
    parser = argparse.ArgumentParser(
        description='Generate Yosys synthesis script for Ibex with instruction checker'
    )
    parser.add_argument('checker_module', help='Path to generated checker module (e.g., my_checker.sv)')
    parser.add_argument('id_stage_modified', help='Path to modified ibex_id_stage.sv with checker')
    parser.add_argument('-o', '--output', default='synth_ibex.ys',
                       help='Output synthesis script file (default: synth_ibex.ys)')
    parser.add_argument('-a', '--aiger-output', default='ibex_core.aig',
                       help='Output AIGER file name (default: ibex_core.aig)')

    args = parser.parse_args()

    # Generate the script
    script = generate_synthesis_script(args.checker_module, args.id_stage_modified, args.aiger_output)

    # Write to file
    with open(args.output, 'w') as f:
        f.write(script)

    print(f"Generated synthesis script: {args.output}")
    print(f"  Checker module:     {args.checker_module}")
    print(f"  Modified ID stage:  {args.id_stage_modified}")
    print(f"  Output AIGER:       {args.aiger_output}")
    print()
    print(f"Run with: synlig -s {args.output}")

if __name__ == '__main__':
    main()
