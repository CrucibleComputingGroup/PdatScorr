#!/usr/bin/env python3
"""
Step 4: Actually apply equivalences to optimize the circuit.

Uses Yosys 'connect -set' to substitute equivalent signals,
then removes dead logic.
"""

import sys
import json
import subprocess
from pathlib import Path

def generate_equivalence_script(rtlil_file, equivalences, output_rtlil, output_verilog):
    """Generate Yosys script that applies equivalences."""

    script = f"""# Apply proven equivalences to optimize circuit

read_rtlil {rtlil_file}

# Before applying equivalences
stat

"""

    # For each equivalence, substitute one signal with the other
    for sig_a, sig_b in equivalences:
        script += f"# Proven: {sig_a} ≡ {sig_b}\n"
        script += f"connect -set {sig_a} {sig_b}\n"
        script += "\n"

    script += f"""# Remove dead logic after substitutions
opt_clean
opt -full

# After applying equivalences
stat

# Write optimized design
write_rtlil {output_rtlil}
write_verilog -noattr {output_verilog}
"""

    return script

def main():
    if len(sys.argv) != 3:
        print("Usage: step4_apply_equiv_real.py <proven_equivalences.json> <rtlil_file>")
        print("")
        print("Example:")
        print("  step4_apply_equiv_real.py output/proven_equivalences.json output/simple_mux_prepared.il")
        print("")
        print("Actually applies equivalences to optimize the circuit")
        sys.exit(1)

    equiv_file = Path(sys.argv[1])
    rtlil_file = Path(sys.argv[2])

    if not equiv_file.exists():
        print(f"ERROR: Equivalences file not found: {equiv_file}")
        sys.exit(1)

    if not rtlil_file.exists():
        print(f"ERROR: RTLIL file not found: {rtlil_file}")
        sys.exit(1)

    output_dir = equiv_file.parent
    module_name = rtlil_file.stem.replace('_prepared', '')

    print("=" * 80)
    print("STEP 4: APPLYING EQUIVALENCES TO OPTIMIZE CIRCUIT")
    print("=" * 80)
    print()

    # Load proven equivalences
    with open(equiv_file, 'r') as f:
        data = json.load(f)
        equivalences = data.get('proven_equivalences', [])

    if not equivalences:
        print("No equivalences to apply!")
        return

    print(f"Applying {len(equivalences)} proven equivalence(s):")
    for sig_a, sig_b in equivalences:
        print(f"  {sig_a} ≡ {sig_b}")
    print()

    # Generate script
    output_rtlil = output_dir / f"{module_name}_opt_equiv.il"
    output_verilog = output_dir / f"{module_name}_opt_equiv.v"
    script_file = output_dir / "apply_equiv.ys"

    script = generate_equivalence_script(rtlil_file, equivalences, output_rtlil, output_verilog)

    with open(script_file, 'w') as f:
        f.write(script)

    print(f"Generated Yosys script: {script_file}")

    # Run Yosys
    print("\nApplying equivalences with Yosys...")
    result = subprocess.run(
        ['yosys', '-s', str(script_file)],
        capture_output=True,
        text=True
    )

    if result.returncode != 0:
        print("ERROR: Yosys failed")
        print(result.stderr)
        sys.exit(1)

    # Extract before/after stats
    lines = result.stdout.split('\n')
    before_cells = None
    after_cells = None

    for i, line in enumerate(lines):
        if 'Before applying equivalences' in lines[max(0,i-5):i+1]:
            if 'Number of cells:' in line:
                before_cells = int(line.split(':')[1].strip())
        if 'After applying equivalences' in lines[max(0,i-5):i+1]:
            if 'Number of cells:' in line:
                after_cells = int(line.split(':')[1].strip())

    print()
    print("=" * 80)
    print("RESULTS")
    print("=" * 80)

    if before_cells and after_cells:
        removed = before_cells - after_cells
        pct = 100.0 * removed / before_cells if before_cells > 0 else 0

        print(f"  Before: {before_cells} cells")
        print(f"  After:  {after_cells} cells")
        print(f"  Removed: {removed} cells ({pct:.1f}%)")
    else:
        print("  (Could not extract statistics)")

    print()
    print(f"  Optimized RTLIL:   {output_rtlil}")
    print(f"  Optimized Verilog: {output_verilog}")
    print()
    print("✓ Equivalences applied successfully!")
    print()

if __name__ == '__main__':
    main()
