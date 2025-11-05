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
    
    # Determine which original file this replaces
    if "ibex_alu" in error_injected_rtl.name:
        original_filename = "ibex_alu.sv"
        injection_type = "odc_error"
    elif "ibex_id_stage" in error_injected_rtl.name:
        original_filename = "ibex_id_stage.sv"
        injection_type = "isa"
    else:
        raise ValueError(f"Unknown RTL file type: {error_injected_rtl.name}")
    
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
    _generate_synthesis_script(
        config=config,
        synth_script=synth_script,
        id_stage_modified=id_stage_modified,
        alu_modified=error_injected_rtl if "alu" in original_filename else None,
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
    output_aig: Path
) -> None:
    """
    Generate Yosys synthesis script using config file.
    
    Args:
        config: CoreConfig object with synthesis settings
        synth_script: Path to output synthesis script
        id_stage_modified: Modified ID stage with assumptions
        alu_modified: Modified ALU with error injection (if applicable)
        output_aig: Output AIGER path
    """
    core_root = Path(config.synthesis.core_root_resolved)
    
    # Build include paths from config
    include_args_list = [f"-I{core_root / inc}" for inc in config.synthesis.include_dirs]
    include_args = " \\\n  ".join(include_args_list)

    # Build list of all source files (with modifications)
    source_file_list = []

    for source_file in config.synthesis.source_files:
        source_path = core_root / source_file

        # Use modified versions if they exist
        # Since Synlig runs from same dir as modified files, use basename for those
        if source_file == "rtl/ibex_id_stage.sv":
            source_file_list.append(id_stage_modified.name)
        elif source_file == "rtl/ibex_alu.sv" and alu_modified:
            source_file_list.append(alu_modified.name)
        else:
            source_file_list.append(str(source_path))

    file_args = " \\\n  ".join(source_file_list)

    script_lines = [
        "# Auto-generated synthesis script for ODC error-injected circuit",
        f"# Core: {config.core_name}",
        "",
        "# Set include directories",
    ]

    for inc_dir in include_args_list:
        script_lines.append(f"verilog_defaults -add {inc_dir}")

    script_lines.extend([
        "",
        "# Read all source files together so packages are available to all modules",
        f"read_systemverilog \\",
        f"  {include_args} \\",
        f"  {file_args}",
        "",
    ])
    
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
