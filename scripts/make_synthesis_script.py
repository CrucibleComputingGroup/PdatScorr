#!/usr/bin/env python3
"""
Generate a Yosys/Synlig synthesis script for Ibex with instruction checker.
"""

import argparse

def generate_synthesis_script(id_stage_modified: str, output_aig: str, ibex_root: str = None, writeback_stage: bool = False) -> str:
    """Generate the Yosys synthesis script."""

    import os

    # Determine Ibex core path:
    # 1. Use provided ibex_root argument
    # 2. Fall back to IBEX_ROOT environment variable
    # 3. Try ../PdatCoreSim/cores/ibex
    # 4. Try ../CoreSim/cores/ibex
    # 5. Error if none found
    if ibex_root is None:
        ibex_root = os.environ.get('IBEX_ROOT')

        if ibex_root is None:
            # Try both PdatCoreSim and CoreSim
            candidates = ['../PdatCoreSim/cores/ibex', '../CoreSim/cores/ibex']
            for candidate in candidates:
                candidate_abs = os.path.abspath(os.path.expanduser(candidate))
                if os.path.isdir(candidate_abs):
                    ibex_root = candidate_abs
                    break

            if ibex_root is None:
                raise FileNotFoundError(
                    "Could not find Ibex core directory. Tried:\n" +
                    "\n".join(f"  - {c}" for c in candidates) +
                    "\n\nPlease set IBEX_ROOT environment variable or use --ibex-root argument"
                )

    # Convert to absolute path
    ibex_root = os.path.abspath(os.path.expanduser(ibex_root))

    script = f"""# Synlig script to convert ibex core (with inline assumptions) to AIGER format
# Auto-generated synthesis script
# Ibex core path: {ibex_root}

# Set include directories
verilog_defaults -add -I{ibex_root}/rtl
verilog_defaults -add -I{ibex_root}/shared/rtl
verilog_defaults -add -I{ibex_root}/vendor/lowrisc_ip/ip/prim/rtl
verilog_defaults -add -I{ibex_root}/vendor/lowrisc_ip/dv/sv/dv_utils

# Read all Ibex files together so packages are available to all modules
# This ensures ibex_pkg is visible to all modules that import it
read_systemverilog \\
  -I{ibex_root}/rtl \\
  -I{ibex_root}/shared/rtl \\
  -I{ibex_root}/vendor/lowrisc_ip/ip/prim/rtl \\
  -I{ibex_root}/vendor/lowrisc_ip/dv/sv/dv_utils \\
  {ibex_root}/rtl/ibex_pkg.sv \\
  {ibex_root}/rtl/ibex_alu.sv \\
  {ibex_root}/rtl/ibex_branch_predict.sv \\
  {ibex_root}/rtl/ibex_compressed_decoder.sv \\
  {ibex_root}/rtl/ibex_controller.sv \\
  {ibex_root}/rtl/ibex_counter.sv \\
  {ibex_root}/rtl/ibex_cs_registers.sv \\
  {ibex_root}/rtl/ibex_csr.sv \\
  {ibex_root}/rtl/ibex_decoder.sv \\
  {ibex_root}/rtl/ibex_dummy_instr.sv \\
  {ibex_root}/rtl/ibex_ex_block.sv \\
  {ibex_root}/rtl/ibex_fetch_fifo.sv \\
  ./{id_stage_modified} \\
  {ibex_root}/rtl/ibex_if_stage.sv \\
  {ibex_root}/rtl/ibex_load_store_unit.sv \\
  {ibex_root}/rtl/ibex_multdiv_fast.sv \\
  {ibex_root}/rtl/ibex_multdiv_slow.sv \\
  {ibex_root}/rtl/ibex_pmp.sv \\
  {ibex_root}/rtl/ibex_prefetch_buffer.sv \\
  {ibex_root}/rtl/ibex_register_file_ff.sv \\
  {ibex_root}/rtl/ibex_wb_stage.sv \\
  {ibex_root}/vendor/lowrisc_ip/ip/prim/rtl/prim_assert.sv \\
  {ibex_root}/rtl/ibex_core.sv

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
write_aiger -zinit {output_aig}_yosys.aig

# NOTE: External ABC will be run by the shell script to optimize this AIGER:
#   abc -c "read_aiger {output_aig}_yosys.aig; strash; scorr; dc2; dretime; write_aiger {output_aig}_post_abc.aig"
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
    parser.add_argument('--ibex-root', default=None,
                       help='Path to Ibex core (default: $IBEX_ROOT or auto-detect ../PdatCoreSim/cores/ibex or ../CoreSim/cores/ibex)')
    parser.add_argument('--writeback-stage', action='store_true',
                       help='Enable 3-stage pipeline with separate writeback stage (default: 2-stage)')

    args = parser.parse_args()

    # Generate the script
    script = generate_synthesis_script(args.id_stage_modified, args.aiger_output, args.ibex_root, args.writeback_stage)

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
