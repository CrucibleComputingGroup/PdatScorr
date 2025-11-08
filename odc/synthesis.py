#!/usr/bin/env python3
"""
Synthesis module for error-injected circuits.

Handles synthesizing modified RTL (with error injection) to AIGER format
for SEC checking.
"""

import sys
import subprocess
from pathlib import Path
from typing import Optional

# Add scripts to path for config loader
sys.path.insert(0, str(Path(__file__).parent.parent / "scripts"))

from config_loader import ConfigLoader
from synthesis_utils import process_source_files


def synthesize_error_injected_circuit(
    error_injected_rtl: Path,
    dsl_file: Path,
    output_dir: Path,
    config_file: Path,
    k_depth: int = 2
) -> Optional[Path]:
    """
    Synthesize error-injected circuit to AIGER.
    
    Uses config file to determine core structure and file locations.
    
    Args:
        error_injected_rtl: Modified RTL file (e.g., ibex_alu_odc_*.sv)
        dsl_file: DSL file with constraints
        output_dir: Output directory for synthesis products
        config_file: Core configuration file (e.g., configs/ibex.yaml)
        k_depth: Pipeline depth for ABC optimization
        
    Returns:
        Path to generated AIGER file, or None if synthesis failed
    """
    output_dir.mkdir(parents=True, exist_ok=True)
    
    # Load config
    config = ConfigLoader.load_config(str(config_file))
    core_root = Path(config.synthesis.core_root_resolved)
    
    # Determine which original file this replaces (use generic pattern matching)
    is_alu = "alu" in error_injected_rtl.name.lower()
    is_id_stage = "id_stage" in error_injected_rtl.name.lower() or "control" in error_injected_rtl.name.lower()
    is_regfile = "register_file" in error_injected_rtl.name.lower() or "regfile" in error_injected_rtl.name.lower()

    if is_alu:
        injection_type = "odc_error"
    elif is_id_stage:
        injection_type = "isa"
    elif is_regfile:
        injection_type = "regfile"  # New type for register file optimizations
    else:
        # Default to ISA injection
        injection_type = "isa"

    # Create output base name
    base_name = error_injected_rtl.stem
    output_base = output_dir / base_name
    
    # Generate assumptions from DSL
    assumptions_file = output_base.with_name(f"{base_name}_assumptions.sv")
    print(f"      Generating assumptions...")
    result = subprocess.run(
        ["pdat-dsl", "codegen", str(dsl_file), str(assumptions_file)],
        capture_output=True,
        text=True
    )
    
    if result.returncode != 0:
        print(f"      ERROR: Failed to generate assumptions")
        print(result.stderr)
        return None
    
    # Get ISA injection point from config (by constraint_type)
    isa_injection = config.get_injection("isa")
    if not isa_injection:
        print(f"      ERROR: No ISA injection point found in config")
        return None
    
    # Create modified ID stage with assumptions
    id_stage_modified = output_base.with_name(f"{base_name}_id_stage.sv")
    original_id_stage = core_root / isa_injection.source_file
    
    print(f"      Injecting assumptions into ID stage...")
    result = subprocess.run(
        ["python3", "scripts/inject_checker.py",
         "--assumptions-file", str(assumptions_file),
         str(original_id_stage),
         str(id_stage_modified)],
        capture_output=True,
        text=True
    )
    
    if result.returncode != 0:
        print(f"      ERROR: Failed to inject assumptions")
        print(result.stderr)
        return None
    
    # Generate synthesis script
    synth_script = output_base.with_name(f"{base_name}_synth.ys")
    yosys_aig = output_base.with_name(f"{base_name}_yosys.aig")
    
    print(f"      Generating synthesis script...")

    # Check if there's an optimized register file in the same directory
    # Look for any file matching *register_file*_optimized.sv
    regfile_optimized = None
    for candidate in error_injected_rtl.parent.glob("*register_file*_optimized.sv"):
        regfile_optimized = candidate
        print(f"      Found optimized register file: {regfile_optimized.name}")
        break

    _generate_synthesis_script(
        config=config,
        synth_script=synth_script,
        id_stage_modified=id_stage_modified,
        alu_modified=error_injected_rtl if is_alu else None,
        regfile_modified=regfile_optimized,
        output_aig=yosys_aig
    )
    
    # Run Synlig
    print(f"      Running Synlig (this may take a few minutes)...")
    synlig_log = output_base.with_name(f"{base_name}_synlig.log")

    # Run Synlig from error_injection directory (parent of synth_script)
    # This ensures slpp_all is created there and paths are correct
    synlig_dir = synth_script.parent
    result = subprocess.run(
        ["synlig", "-s", synth_script.name],
        capture_output=True,
        text=True,
        timeout=600,
        cwd=synlig_dir
    )
    
    # Save log
    with open(synlig_log, 'w') as f:
        f.write(result.stdout)
        f.write(result.stderr)
    
    if result.returncode != 0:
        print(f"      ERROR: Synlig failed (see {synlig_log})")
        return None
    
    # Verify AIGER was created
    if not yosys_aig.exists():
        print(f"      ERROR: AIGER file not created: {yosys_aig}")
        return None
    
    print(f"      Synthesis complete: {yosys_aig.name}")
    return yosys_aig


def _generate_synthesis_script(
    config: 'CoreConfig',
    synth_script: Path,
    id_stage_modified: Path,
    alu_modified: Optional[Path],
    output_aig: Path,
    regfile_modified: Optional[Path] = None
) -> None:
    """
    Generate Yosys synthesis script using config file.

    Args:
        config: CoreConfig object with synthesis settings
        synth_script: Path to output synthesis script
        id_stage_modified: Modified ID stage with assumptions
        alu_modified: Modified ALU with error injection (if applicable)
        regfile_modified: Modified register file with unused registers tied off (if applicable)
        output_aig: Output AIGER path
    """
    core_root = Path(config.synthesis.core_root_resolved)
    
    # Build include paths from config
    # IMPORTANT: Only include vendor/package directories, NOT main rtl directory
    # to avoid conflicts when we have modified versions of RTL files
    include_args_list = []
    for inc in config.synthesis.include_dirs:
        # Skip main rtl directory to avoid module name conflicts
        if inc == "rtl" or inc.endswith("/rtl"):
            continue
        include_args_list.append(f"-I{core_root / inc}")
    include_args = " \\\n  ".join(include_args_list)

    # Build list of all source files (with modifications)
    # Build injection map for process_source_files utility
    injection_to_file_map = {}
    for inj in config.injections:
        injection_to_file_map[inj.source_file] = inj.name

    # Build modified files map
    modified_map = {}

    # ISA injection
    isa_injection = config.get_injection("isa")
    if isa_injection:
        modified_map[isa_injection.name] = str(id_stage_modified.absolute())

    # ODC error injection (ALU)
    if alu_modified:
        odc_injection = config.get_injection("odc_error")
        if odc_injection:
            modified_map[odc_injection.name] = str(alu_modified.absolute())

    # Register file optimization
    if regfile_modified:
        rf_injection = config.get_injection("odc_opt")
        if rf_injection:
            modified_map[rf_injection.name] = str(regfile_modified.absolute())

    # Use shared utility to process all source files
    source_file_list = process_source_files(
        source_files=config.synthesis.source_files,
        core_root=core_root,
        injection_map=injection_to_file_map,
        modified_files=modified_map
    )

    file_args = " \\\n  ".join(source_file_list)

    # Separate modified files from original files
    modified_file_list = []
    original_file_list = []

    for source in source_file_list:
        # Modified files use absolute paths
        if source.startswith('/'):
            modified_file_list.append(source)
        else:
            original_file_list.append(source)

    script_lines = [
        "# Auto-generated synthesis script for ODC error-injected circuit",
        f"# Core: {config.core_name}",
        "",
        "# Set include directories (for vendor libs and packages only)",
    ]

    for inc_dir in include_args_list:
        script_lines.append(f"verilog_defaults -add {inc_dir}")

    script_lines.extend([
        "",
        "# Read all source files together so packages are available to all modules",
        "# Modified files use absolute paths to take precedence over include path versions",
        f"read_systemverilog \\",
    ])

    # Add include args to read command
    for inc_arg in include_args_list:
        script_lines.append(f"  {inc_arg} \\")

    # Add all source files (modified with absolute paths come first due to sorting)
    for source in sorted(source_file_list, key=lambda s: (0 if s.startswith('/') else 1, s)):
        script_lines.append(f"  {source} \\")

    script_lines.append("")
    
    # Add full synthesis flow (same as main synthesis script)
    # Use basename for output since Synlig runs from same directory
    script_lines.extend([
        "",
        "# Prepare design for synthesis",
        f"hierarchy -check -top {config.synthesis.top_module}",
        "flatten",
        "",
        "# Basic optimization preserving sequential structure",
        "proc",
        "opt",
        "memory",
        "techmap",
        "opt",
        "",
        "# Simplify DFFs for AIGER export",
        "async2sync",
        "simplemap",
        "dfflegalize -cell $_DFF_P_ 01 -mince 99999",
        "clean",
        "",
        "# Prepare for AIGER",
        "setundef -zero",
        "aigmap",
        "clean",
        "",
        "# Write AIGER",
        f"write_aiger -zinit {output_aig.name}",
        ""
    ])
    
    with open(synth_script, 'w') as f:
        f.write('\n'.join(script_lines))


def main():
    """CLI for testing synthesis."""
    import argparse
    
    parser = argparse.ArgumentParser(description="Synthesize error-injected circuit")
    parser.add_argument("error_rtl", type=Path, help="Error-injected RTL file")
    parser.add_argument("dsl_file", type=Path, help="DSL file")
    parser.add_argument("--output-dir", type=Path, required=True, help="Output directory")
    parser.add_argument("--config", type=Path, default=Path("configs/ibex.yaml"),
                       help="Core config file")
    parser.add_argument("--k-depth", type=int, default=2, help="Pipeline depth")
    
    args = parser.parse_args()
    
    result = synthesize_error_injected_circuit(
        args.error_rtl,
        args.dsl_file,
        args.output_dir,
        args.config,
        args.k_depth
    )
    
    if result:
        print(f"Success: {result}")
        return 0
    else:
        print("Synthesis failed")
        return 1


if __name__ == "__main__":
    sys.exit(main())
