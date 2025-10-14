#!/usr/bin/env python3
"""
Step 1: Prepare RTL for equivalence checking.

Converts SystemVerilog to structural RTL netlist using Yosys,
preserving hierarchy and signal names.
"""

import sys
import subprocess
from pathlib import Path

def generate_yosys_script(rtl_files, top_module, output_rtlil, output_smt2):
    """Generate Yosys script to prepare RTL."""

    # Build file list
    files_str = " \\\n  ".join(rtl_files)

    script = f"""# Prepare RTL for equivalence checking
# Convert processes to structural netlist while preserving hierarchy

# Read RTL
read_verilog -sv {files_str}

# Set top module
hierarchy -check -top {top_module}

# Convert processes to gates + FFs
proc

# Optimize but preserve hierarchy
opt

# Show statistics before flattening
stat

# Save intermediate RTLIL (with hierarchy)
write_rtlil {output_rtlil}

# Generate SMT2 model (for formal checking)
async2sync
dffunmap
write_smt2 -wires -stbv -stdt {output_smt2}
"""

    return script

def prepare_rtl(rtl_files, top_module, output_dir):
    """Prepare RTL design for equivalence checking."""

    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    output_rtlil = output_dir / f"{top_module}_prepared.il"
    output_smt2 = output_dir / f"{top_module}_smt.smt2"
    script_path = output_dir / "prepare.ys"

    # Generate Yosys script
    script = generate_yosys_script(rtl_files, top_module, output_rtlil, output_smt2)

    with open(script_path, 'w') as f:
        f.write(script)

    print(f"Generated Yosys script: {script_path}")
    print(f"Running Yosys to prepare RTL...")

    # Run Yosys
    result = subprocess.run(
        ['yosys', '-s', str(script_path)],
        capture_output=True,
        text=True
    )

    if result.returncode != 0:
        print("ERROR: Yosys preparation failed")
        print(result.stderr)
        return None

    print(f"✓ Generated RTLIL: {output_rtlil}")
    print(f"✓ Generated SMT2: {output_smt2}")

    return {
        'rtlil': output_rtlil,
        'smt2': output_smt2
    }

def main():
    if len(sys.argv) < 3:
        print("Usage: step1_prepare_rtl.py <top_module> <output_dir> <rtl_files...>")
        print("")
        print("Example:")
        print("  step1_prepare_rtl.py decoder output/ design.v decoder.v")
        print("")
        print("Converts RTL to structural netlist for equivalence checking")
        sys.exit(1)

    top_module = sys.argv[1]
    output_dir = sys.argv[2]
    rtl_files = sys.argv[3:]

    # Check files exist
    for f in rtl_files:
        if not Path(f).exists():
            print(f"ERROR: File not found: {f}")
            sys.exit(1)

    # Prepare RTL
    result = prepare_rtl(rtl_files, top_module, output_dir)

    if result:
        print("\nNext step: Run simulation to collect value vectors")
        print(f"  python3 scripts/step2_simulate.py {result['rtlil']}")

if __name__ == '__main__':
    main()
