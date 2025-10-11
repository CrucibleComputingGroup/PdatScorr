#!/usr/bin/env python3
"""
Generate a Yosys/Synlig synthesis script for Ibex with instruction checker.
"""

import argparse

def generate_synthesis_script(id_stage_modified: str, output_aig: str, writeback_stage: bool = False) -> str:
    """Generate the Yosys synthesis script."""

    import os

    # Use absolute paths for include directories to ensure they're found
    cwd = os.getcwd()

    script = f"""# Synlig script to convert ibex core (with inline assumptions) to AIGER format
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
  ./cores/ibex/rtl/ibex_core.sv

"""

    # Add parameter override if writeback stage requested
    if writeback_stage:
        script += """# Enable 3-stage pipeline (IF, ID/EX, WB) instead of default 2-stage
chparam -set WritebackStage 1 ibex_core

"""

    script += f"""# Prepare the design for synthesis using ibex_core as top
hierarchy -check -top ibex_core

# Flatten to enable sequential optimizations across module boundaries
flatten

# Do basic optimization but preserve sequential structure (registers)
# proc converts processes to netlists but keeps flip-flops
proc
opt

# Map memory and do basic synthesis preserving sequential structure
# Keep $assume cells intact - they will be exported as AIGER constraints (C field)
memory
techmap
opt

# Export to AIGER format which natively supports constraints (assumptions)
# AIGER is better than BLIF because:
# 1. Constraints are part of the format
# 2. ABC can read and use them for optimization
# 3. Sequential structure is preserved

# Simplify all DFFs to the most basic type for AIGER export
# AIGER only supports simple positive-edge D-type flip-flops

# Step 1: Convert async resets to sync (becomes mux + simple DFF)
async2sync

# Step 2: Use simplemap to break down high-level DFF types to gate-level primitives
simplemap

# Step 3: Use dfflegalize to convert ALL DFF types to simple $_DFF_P_ only
# Allow init values 0 and 1 - write_aiger will handle them
# This expands resets, enables, etc. into combinational logic + simple DFF
# Use -mince 99999 to force expansion of ALL clock enables (don't keep any)
dfflegalize -cell $_DFF_P_ 01 -mince 99999

# Do NOT run opt here - it will re-add enables via opt_dff!
# Just run clean to remove unused wires
clean

# Step 4: Replace undefined (x/z) values with defined values
# AIGER doesn't support x or z
setundef -zero

# Step 5: Convert all combinational logic to AIG (AND + NOT)
aigmap

# Clean up but don't optimize DFFs
clean

# Export to AIGER with constraints
# AIGER format: latches + AND gates + constraints (bad state properties)
# -zinit maps init values to zero during export
write_aiger -zinit {output_aig}_pre_abc.aig

# NOTE: External ABC will be run by the shell script to optimize this AIGER:
#   abc -c "read_aiger {output_aig}_pre_abc.aig; strash; scorr; dc2; dretime; write_aiger {output_aig}_post_abc.aig"
# The optimized AIGER ({{output_aig}}_post_abc.aig) is the final output for sequential optimization.

# For gate-level synthesis, the synth_to_gates.sh script will read the optimized AIGER
# and map it to the PDK standard cells.
"""
    return script

def main():
    parser = argparse.ArgumentParser(
        description='Generate Yosys synthesis script for Ibex with instruction assumptions'
    )
    parser.add_argument('id_stage_modified', help='Path to modified ibex_id_stage.sv with inline assumptions')
    parser.add_argument('-o', '--output', default='synth_ibex.ys',
                       help='Output synthesis script file (default: synth_ibex.ys)')
    parser.add_argument('-a', '--aiger-output', default='ibex_core.aig',
                       help='Output AIGER file base name (default: ibex_core.aig)')
    parser.add_argument('--writeback-stage', action='store_true',
                       help='Enable 3-stage pipeline with separate writeback stage (default: 2-stage)')

    args = parser.parse_args()

    # Generate the script
    script = generate_synthesis_script(args.id_stage_modified, args.aiger_output, args.writeback_stage)

    # Write to file
    with open(args.output, 'w') as f:
        f.write(script)

    print(f"Generated synthesis script: {args.output}")
    print(f"  Modified ID stage:  {args.id_stage_modified}")
    print(f"  Output AIGER:       {args.aiger_output}")
    print()
    print(f"Run with: synlig -s {args.output}")

if __name__ == '__main__':
    main()
