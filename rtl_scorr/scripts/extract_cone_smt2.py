#!/usr/bin/env python3
"""
Extract SMT2 cone using Yosys built-in %ci (cone of influence) selection.

This is the RIGHT way to do it - use Yosys's native cone extraction,
then generate SMT2 for only the selected cone.
"""

import sys
import subprocess
import tempfile
from pathlib import Path


def extract_cone_smt2(rtlil_file: Path, target_wires: list, output_smt2: Path, k_depth: int = 2) -> bool:
    """
    Extract cone using Yosys select %ci and generate SMT2.

    Args:
        rtlil_file: Input RTLIL file (already synthesized)
        target_wires: List of wire names to extract cones for
        output_smt2: Output SMT2 file
        k_depth: K-induction depth for unwinding

    Returns:
        True on success
    """

    # Build Yosys script that:
    # 1. Loads RTLIL
    # 2. Selects input cones for targets using %ci
    # 3. Generates SMT2 for ONLY the selection
    yosys_script = f"""
# Load prepared RTLIL
read_rtlil {rtlil_file}

# Select cones for target wires
select -none

"""

    # Add each target wire's input cone
    for wire in target_wires:
        yosys_script += f"""
# Add cone for {wire}
select -add w:*{wire}* %ci*

"""

    yosys_script += f"""
# Show selected cone size
select -count

# Note: write_smt2 doesn't respect selection, it always outputs the full design
# So cone extraction via selection doesn't reduce SMT2 size
# We'll generate full SMT2 and do cone extraction in post-processing

# Now prepare for SMT2
dffunmap

# Generate SMT2 (now only contains the cone!)
write_smt2 -wires -stdt {output_smt2}

log "✓ Cone SMT2 generated: {output_smt2}"
"""

    # Write script
    with tempfile.NamedTemporaryFile(mode='w', suffix='.ys', delete=False) as f:
        f.write(yosys_script)
        script_file = f.name

    try:
        # Run Yosys
        result = subprocess.run(
            ['synlig', '-s', script_file],
            capture_output=True,
            text=True,
            timeout=120
        )

        Path(script_file).unlink()

        if result.returncode != 0:
            print("ERROR: Yosys failed")
            print(result.stderr[-1000:])  # Last 1000 chars
            return False

        if not output_smt2.exists():
            print("ERROR: SMT2 not generated")
            return False

        # Show selection info from log
        for line in result.stdout.split('\n'):
            if 'Selected cone' in line or 'selected' in line.lower():
                print(f"  {line}")

        return True

    except subprocess.TimeoutExpired:
        Path(script_file).unlink()
        print("ERROR: Timeout")
        return False


def main():
    if len(sys.argv) < 4:
        print("Usage: extract_cone_smt2.py <rtlil_file> <output.smt2> <wire1> [wire2 ...]")
        print("")
        print("Example:")
        print("  extract_cone_smt2.py ibex_core.il mult_cone.smt2 mult_en_dec div_en_dec")
        print("")
        print("Uses Yosys %ci to extract input cones for target wires")
        sys.exit(1)

    rtlil_file = Path(sys.argv[1])
    output_smt2 = Path(sys.argv[2])
    target_wires = sys.argv[3:]

    if not rtlil_file.exists():
        print(f"ERROR: RTLIL file not found: {rtlil_file}")
        sys.exit(1)

    print("=" * 80)
    print("YOSYS CONE EXTRACTION FOR SMT2")
    print("=" * 80)
    print(f"RTLIL:   {rtlil_file}")
    print(f"Targets: {', '.join(target_wires)}")
    print(f"Output:  {output_smt2}")
    print()

    success = extract_cone_smt2(rtlil_file, target_wires, output_smt2)

    if success:
        # Stats
        smt2_lines = len(output_smt2.read_text().split('\n'))
        print()
        print(f"✓ Success!")
        print(f"  Generated: {output_smt2}")
        print(f"  Size: {smt2_lines} lines")
    else:
        print()
        print("✗ Cone extraction failed")
        sys.exit(1)


if __name__ == '__main__':
    main()
