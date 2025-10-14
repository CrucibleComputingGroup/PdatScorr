#!/usr/bin/env python3
"""
Use Yosys's built-in equivalence checking to find constant RTL signals.

This uses Yosys's equiv_make/equiv_induct commands to check which signals
are constant under the given constraints, preserving RTL signal names.
"""

import sys
import subprocess
import tempfile
from pathlib import Path

def create_yosys_equiv_script(id_stage_path, output_report):
    """
    Generate Yosys script that checks for constant signals using equiv_induct.
    """

    import os
    cwd = os.getcwd()

    script = f"""# Yosys equivalence checking for RTL dead code detection
# Preserves hierarchy to report signal names

read_systemverilog \\
  -I{cwd}/cores/ibex/rtl \\
  -I{cwd}/cores/ibex/shared/rtl \\
  -I{cwd}/cores/ibex/vendor/lowrisc_ip/ip/prim/rtl \\
  -I{cwd}/cores/ibex/vendor/lowrisc_ip/dv/sv/dv_utils \\
  -DYOSYS=1 -DSYNTHESIS=1 \\
  ./cores/ibex/rtl/ibex_pkg.sv \\
  ./cores/ibex/rtl/ibex_decoder.sv \\
  ./cores/ibex/rtl/ibex_controller.sv \\
  {id_stage_path}

# Use ID stage as top
hierarchy -check -top ibex_id_stage

# Process but preserve hierarchy
proc
opt

# Show current module structure
ls

# Show all signals
stat

# Create equivalence problem
# This will find signals equivalent to constants
equiv_make

# Run simple (combinational) equivalence first
equiv_simple -undef

# Show status after simple equivalence
equiv_status

# Run induction-based equivalence (k=2)
equiv_induct -undef

# Show final equivalence status
equiv_status

# Optimize based on proven equivalences
equiv_opt

# Clean up
opt_clean

# Show final statistics
stat

# Write report
tee -a {output_report}
"""

    return script

def run_yosys_equiv_check(id_stage_path, output_report):
    """Run Yosys equivalence checking."""

    script = create_yosys_equiv_script(id_stage_path, output_report)

    # Write script to temp file
    with tempfile.NamedTemporaryFile(mode='w', suffix='.ys', delete=False) as f:
        f.write(script)
        script_path = f.name

    print("Running Yosys equivalence checking...")
    print(f"Report will be saved to: {output_report}")
    print()

    # Run with synlig for SystemVerilog support
    result = subprocess.run(
        ['synlig', '-s', script_path],
        capture_output=True,
        text=True,
        timeout=120
    )

    # Clean up
    Path(script_path).unlink()

    return result.stdout, result.stderr, result.returncode

def parse_yosys_output(stdout):
    """Parse Yosys output to extract signal information."""

    findings = {
        'signals_before': [],
        'signals_after': [],
        'constant_signals': []
    }

    # Extract signal lists
    current_section = None
    for line in stdout.split('\n'):
        if '=== Decoder Signals Before Optimization ===' in line:
            current_section = 'before'
        elif '=== Final Decoder Signals After Optimization ===' in line:
            current_section = 'after'
        elif '=== Constant Signal Detection ===' in line:
            current_section = 'constants'
        elif current_section and line.strip() and not line.startswith('==='):
            # Parse signal names from Yosys ls output
            if current_section == 'before':
                findings['signals_before'].append(line.strip())
            elif current_section == 'after':
                findings['signals_after'].append(line.strip())
            elif current_section == 'constants':
                findings['constant_signals'].append(line.strip())

    return findings

def main():
    if len(sys.argv) != 2:
        print("Usage: yosys_rtl_equiv_check.py <output_base>")
        print("")
        print("Example: yosys_rtl_equiv_check.py output/ibex_optimized")
        print("")
        print("Uses Yosys equiv_induct to find constant RTL signals")
        sys.exit(1)

    base_path = sys.argv[1]
    id_stage_modified = f"{base_path}_id_stage.sv"
    output_report = f"{base_path}_rtl_equiv_report.txt"

    if not Path(id_stage_modified).exists():
        print(f"ERROR: Modified ID stage not found: {id_stage_modified}")
        sys.exit(1)

    print("=" * 80)
    print(" " * 20 + "YOSYS RTL EQUIVALENCE CHECKING")
    print("=" * 80)
    print()

    # Run Yosys equivalence check
    stdout, stderr, returncode = run_yosys_equiv_check(id_stage_modified, output_report)

    if returncode != 0:
        print("ERROR: Yosys equivalence checking failed")
        print(stderr)
        sys.exit(1)

    # Write full output to report file
    with open(output_report, 'w') as f:
        f.write("YOSYS EQUIVALENCE CHECKING OUTPUT\n")
        f.write("=" * 80 + "\n\n")
        f.write(stdout)
        if stderr:
            f.write("\n\nSTDERR:\n")
            f.write(stderr)

    print("✓ Equivalence checking completed")
    print()

    # Parse and summarize
    findings = parse_yosys_output(stdout)

    print("SUMMARY")
    print("-" * 80)
    print(f"  Signals before: {len(findings['signals_before'])}")
    print(f"  Signals after:  {len(findings['signals_after'])}")
    if findings['constant_signals']:
        print(f"  Constant signals detected: {len(findings['constant_signals'])}")
    print()

    # Show relevant sections from stdout
    print("KEY FINDINGS")
    print("-" * 80)

    # Extract the relevant sections
    in_relevant_section = False
    for line in stdout.split('\n'):
        if '===' in line and ('Constant' in line or 'Final Decoder' in line or 'K-Induction' in line):
            in_relevant_section = True
            print(line)
        elif in_relevant_section:
            if line.strip():
                print(line)
            if '===' in line and line.count('===') == 2:
                in_relevant_section = False
                print()

    print()
    print(f"Full report saved to: {output_report}")
    print()

if __name__ == '__main__':
    main()
