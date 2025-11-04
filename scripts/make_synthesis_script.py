#!/usr/bin/env python3
"""
Generate a Yosys/Synlig synthesis script for RISC-V cores with instruction constraints.

Supports both legacy mode (hardcoded paths) and config-based mode (YAML config files).
"""

import argparse
import os
import sys
from pathlib import Path
from typing import Optional, Dict, Any

# Add scripts directory to path for imports
SCRIPT_DIR = Path(__file__).parent
sys.path.insert(0, str(SCRIPT_DIR))

try:
    from config_loader import ConfigLoader, CoreConfig
    CONFIG_SUPPORT = True
except ImportError:
    CONFIG_SUPPORT = False


def generate_synthesis_script_from_config(
    config: 'CoreConfig',
    modified_files: Dict[str, str],
    output_aig: str
) -> str:
    """Generate synthesis script from a config file.

    Args:
        config: Loaded CoreConfig object
        modified_files: Dict mapping injection names to modified file paths
        output_aig: Base name for output AIGER file

    Returns:
        Synthesis script content
    """
    core_root = config.synthesis.core_root_resolved
    include_dirs = config.synthesis.include_dirs
    source_files = config.synthesis.source_files
    top_module = config.synthesis.top_module
    params = config.synthesis.parameters

    # Build include directory flags
    inc_flags = "\n".join(
        f"verilog_defaults -add -I{core_root}/{inc}" for inc in include_dirs)

    # Build source file list, replacing injected files with modified versions
    source_list = []
    injection_map = {inj.source_file: inj.name for inj in config.injections}

    for src_file in source_files:
        # Check if this file should be replaced
        if src_file in injection_map:
            inj_name = injection_map[src_file]
            if inj_name in modified_files:
                # Use modified version
                source_list.append(os.path.abspath(modified_files[inj_name]))
            else:
                # Use original (no injection for this type)
                source_list.append(f"{core_root}/{src_file}")
        else:
            # Use original
            source_list.append(f"{core_root}/{src_file}")

    # Build read_systemverilog command
    include_args = " \\\n  ".join(
        f"-I{core_root}/{inc}" for inc in include_dirs)
    file_args = " \\\n  ".join(source_list)

    script = f"""# Synlig script to synthesize {config.core_name} core with constraints
# Auto-generated synthesis script
# Core: {config.core_name} ({config.architecture})
# Core root: {core_root}

# Set include directories
{inc_flags}

# Read all source files together so packages are available to all modules
read_systemverilog \\
  {include_args} \\
  {file_args}

"""

    # Add parameter overrides
    if params:
        has_params = False
        param_commands = []

        for param_name, param_value in params.items():
            # Special handling for writeback_stage -> WritebackStage
            if param_name == "writeback_stage":
                if param_value:  # Only set if true
                    param_commands.append(
                        f"chparam -set WritebackStage 1 {top_module}\n")
                    has_params = True
                # Skip if false (default)
            elif isinstance(param_value, bool):
                # For other booleans, set them
                param_commands.append(
                    f"chparam -set {param_name} {1 if param_value else 0} {top_module}\n")
                has_params = True
            elif isinstance(param_value, int):
                param_commands.append(
                    f"chparam -set {param_name} {param_value} {top_module}\n")
                has_params = True
            elif isinstance(param_value, str):
                param_commands.append(
                    f"chparam -set {param_name} \"{param_value}\" {top_module}\n")
                has_params = True

        if has_params:
            script += "# Parameter overrides\n"
            script += "".join(param_commands)
            script += "\n"

    script += _generate_synthesis_commands(top_module, output_aig)
    return script


def generate_synthesis_script(id_stage_modified: str, output_aig: str, ibex_root: str = None, writeback_stage: bool = False, core_modified: str = None) -> str:
    """Generate the Yosys synthesis script (legacy mode).

    Args:
        id_stage_modified: Path to modified ibex_id_stage.sv with ISA constraints
        output_aig: Base name for output AIGER file
        ibex_root: Path to Ibex core (optional)
        writeback_stage: Enable 3-stage pipeline (optional)
        core_modified: Path to modified ibex_core.sv with timing constraints (optional)
    """

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

    # Convert modified file paths to absolute paths
    id_stage_modified = os.path.abspath(os.path.expanduser(id_stage_modified))
    if core_modified:
        core_modified = os.path.abspath(os.path.expanduser(core_modified))

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
  {id_stage_modified} \\
  {ibex_root}/rtl/ibex_if_stage.sv \\
  {ibex_root}/rtl/ibex_load_store_unit.sv \\
  {ibex_root}/rtl/ibex_multdiv_fast.sv \\
  {ibex_root}/rtl/ibex_multdiv_slow.sv \\
  {ibex_root}/rtl/ibex_pmp.sv \\
  {ibex_root}/rtl/ibex_prefetch_buffer.sv \\
  {ibex_root}/rtl/ibex_register_file_ff.sv \\
  {ibex_root}/rtl/ibex_wb_stage.sv \\
  {ibex_root}/vendor/lowrisc_ip/ip/prim/rtl/prim_assert.sv \\
  {core_modified if core_modified else ibex_root + '/rtl/ibex_core.sv'}

"""

    # Add parameter override if writeback stage requested
    if writeback_stage:
        script += """# Enable 3-stage pipeline (IF, ID/EX, WB) instead of default 2-stage
chparam -set WritebackStage 1 ibex_core

"""

    script += _generate_synthesis_commands("ibex_core", output_aig)
    return script


def _generate_synthesis_commands(top_module: str, output_aig: str) -> str:
    """Generate common synthesis commands (shared between legacy and config modes)."""
    # Use basename for AIGER output since synlig runs from OUTPUT_DIR
    import os
    output_aig_basename = os.path.basename(output_aig)

    return f"""# Prepare the design for synthesis using {top_module} as top
hierarchy -check -top {top_module}

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
write_aiger -zinit {os.path.abspath(output_aig + "_yosys.aig")}

# NOTE: External ABC will be run by the shell script to optimize this AIGER:
#   abc -c "read_aiger {output_aig}_yosys.aig; strash; scorr; dc2; dretime; write_aiger {output_aig}_post_abc.aig"
# The optimized AIGER ({{output_aig}}_post_abc.aig) is the final output for sequential optimization.

# For gate-level synthesis, the synth_to_gates.sh script will read the optimized AIGER
# and map it to the PDK standard cells.
"""


def main():
    parser = argparse.ArgumentParser(
        description='Generate Yosys synthesis script for RISC-V cores with instruction constraints'
    )

    # Config-based mode
    parser.add_argument(
        '--config', '-c', help='Path to YAML config file (enables config mode)')
    parser.add_argument('--modified-files', nargs='*', default=[],
                        help='Modified files in format name=path (e.g., id_stage_isa=/path/to/file.sv)')

    # Legacy mode arguments
    parser.add_argument('id_stage_modified', nargs='?',
                        help='[Legacy] Path to modified ibex_id_stage.sv with inline assumptions')
    parser.add_argument('--ibex-root', default=None,
                        help='[Legacy] Path to Ibex core')
    parser.add_argument('--writeback-stage', action='store_true',
                        help='[Legacy] Enable 3-stage pipeline')
    parser.add_argument('--core-modified', default=None,
                        help='[Legacy] Path to modified ibex_core.sv with timing constraints')

    # Common arguments
    parser.add_argument('-o', '--output', default='synth_ibex.ys',
                        help='Output synthesis script file (default: synth_ibex.ys)')
    parser.add_argument('-a', '--aiger-output', default='ibex_core.aig',
                        help='Output AIGER file base name (default: ibex_core.aig)')

    args = parser.parse_args()

    # Determine mode
    if args.config:
        # Config-based mode
        if not CONFIG_SUPPORT:
            print("ERROR: Config mode requires PyYAML. Install with: pip install pyyaml")
            return 1

        # Parse modified files argument
        modified_files = {}
        for mf_arg in args.modified_files:
            if '=' not in mf_arg:
                print(f"ERROR: Invalid --modified-files format: {mf_arg}")
                print("Expected format: name=path (e.g., id_stage_isa=/path/to/file.sv)")
                return 1
            name, path = mf_arg.split('=', 1)
            modified_files[name] = path

        # Load config
        try:
            config = ConfigLoader.load_config(args.config)
        except Exception as e:
            print(f"ERROR loading config: {e}")
            return 1

        # Generate script
        try:
            script = generate_synthesis_script_from_config(
                config, modified_files, args.aiger_output)
        except Exception as e:
            print(f"ERROR generating synthesis script: {e}")
            return 1

        print(f"Generated synthesis script (config mode): {args.output}")
        print(f"  Config:      {args.config}")
        print(f"  Core:        {config.core_name}")
        print(f"  Injections:  {len(modified_files)} modified files")

    else:
        # Legacy mode
        if not args.id_stage_modified:
            print("ERROR: id_stage_modified argument required in legacy mode")
            print("Use --config for config-based mode or provide id_stage_modified")
            return 1

        # Generate the script
        script = generate_synthesis_script(
            args.id_stage_modified,
            args.aiger_output,
            args.ibex_root,
            args.writeback_stage,
            args.core_modified
        )

        print(f"Generated synthesis script (legacy mode): {args.output}")
        print(f"  Modified ID stage:  {args.id_stage_modified}")

    # Write to file
    with open(args.output, 'w') as f:
        f.write(script)

    print(f"  Output AIGER:       {args.aiger_output}")
    print()
    print(f"Run with: synlig -s {args.output}")
    return 0


if __name__ == '__main__':
    exit(main())
