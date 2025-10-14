#!/usr/bin/env python3
"""
Hybrid cone extraction:
1. Use Yosys %ci to identify wires in cone
2. Use that list to extract only those signals from SMT2

This combines Yosys's accurate dependency tracking with
text-based SMT2 extraction.
"""

import sys
import subprocess
import tempfile
from pathlib import Path
from smt_cone_extractor_v2 import SimpleSMT2ConeExtractor


def get_cone_wires_from_yosys(rtlil_file: Path, target_wires: list) -> list:
    """
    Use Yosys %ci to get list of wires in cone.

    Returns: List of wire names that are in the input cone
    """

    # Build script to select cone and list it
    yosys_script = f"""
read_rtlil {rtlil_file}

# Select input cone for targets
select -none
"""

    for wire in target_wires:
        yosys_script += f"select -add w:*{wire}* %ci*\n"

    yosys_script += """
# List selected wires
select -list w:*
"""

    # Run Yosys
    with tempfile.NamedTemporaryFile(mode='w', suffix='.ys', delete=False) as f:
        f.write(yosys_script)
        script_file = f.name

    try:
        result = subprocess.run(
            ['synlig', '-s', script_file],
            capture_output=True,
            text=True,
            timeout=30
        )

        Path(script_file).unlink()

        if result.returncode != 0:
            print(f"ERROR: Yosys failed")
            return []

        # Parse output for wire names
        # Format: "ibex_core/id_stage_i.mult_en_dec"
        wire_names = []

        for line in result.stdout.split('\n'):
            line = line.strip()
            # Look for wire listings (module/wirename format)
            if '/' in line and not line.startswith(';') and not line.startswith('--'):
                # Extract just the wire name part (after the /)
                if '/' in line:
                    full_name = line.split()[0]  # Get first token
                    wire = full_name.split('/', 1)[1] if '/' in full_name else full_name
                    wire_names.append(wire)

        return wire_names

    except subprocess.TimeoutExpired:
        Path(script_file).unlink()
        return []


def extract_cone_hybrid(rtlil_file: Path, smt2_file: Path, target_wires: list,
                        output_smt2: Path) -> bool:
    """
    Hybrid approach:
    1. Get cone wire list from Yosys %ci
    2. Extract only those wires from SMT2 file
    """

    print("Step 1: Getting cone wire list from Yosys %ci...")
    cone_wires = get_cone_wires_from_yosys(rtlil_file, target_wires)

    if not cone_wires:
        print("  ERROR: No wires found in cone")
        return False

    print(f"  ✓ Cone contains {len(cone_wires)} wires")
    print(f"    Sample: {cone_wires[:5]}")

    print("\nStep 2: Extracting those wires from SMT2...")
    extractor = SimpleSMT2ConeExtractor(smt2_file)

    # Map wire names to SMT2 function names
    # Wire "mult_en_dec" -> "|ibex_core_n id_stage_i.mult_en_dec|"
    smt_targets = []
    for wire in cone_wires:
        # Try to find matching SMT2 function
        # Check in extractor.definitions for functions containing this wire name
        for func_name in extractor.definitions.keys():
            if wire.replace('.', '\\.') in func_name or wire in func_name:
                smt_targets.append(func_name)
                break

    print(f"  Found {len(smt_targets)} SMT2 functions for cone wires")

    # Extract cone for all these targets
    cone_smt2 = extractor.extract_cone(smt_targets)
    output_smt2.write_text(cone_smt2)

    cone_lines = len(cone_smt2.split('\n'))
    full_lines = len(smt2_file.read_text().split('\n'))
    reduction = 100 * (1 - cone_lines / full_lines)

    print(f"  ✓ Extracted cone:")
    print(f"    Original: {full_lines} lines")
    print(f"    Cone:     {cone_lines} lines")
    print(f"    Reduction: {reduction:.1f}%")

    return True


def main():
    if len(sys.argv) < 5:
        print("Usage: extract_cone_hybrid.py <rtlil> <smt2> <output.smt2> <wire1> [wire2 ...]")
        print("")
        print("Example:")
        print("  extract_cone_hybrid.py ibex.il ibex.smt2 cone.smt2 mult_en_dec div_en_dec")
        print("")
        print("Uses Yosys %ci to find cone, then extracts from SMT2")
        sys.exit(1)

    rtlil_file = Path(sys.argv[1])
    smt2_file = Path(sys.argv[2])
    output_smt2 = Path(sys.argv[3])
    target_wires = sys.argv[4:]

    if not rtlil_file.exists():
        print(f"ERROR: RTLIL not found: {rtlil_file}")
        sys.exit(1)

    if not smt2_file.exists():
        print(f"ERROR: SMT2 not found: {smt2_file}")
        sys.exit(1)

    print("=" * 80)
    print("HYBRID CONE EXTRACTION (Yosys %ci + Text-based SMT2)")
    print("=" * 80)
    print(f"RTLIL:   {rtlil_file}")
    print(f"SMT2:    {smt2_file}")
    print(f"Targets: {', '.join(target_wires)}")
    print(f"Output:  {output_smt2}")
    print()

    success = extract_cone_hybrid(rtlil_file, smt2_file, target_wires, output_smt2)

    if not success:
        sys.exit(1)

    print("\n✓ Hybrid cone extraction complete!")


if __name__ == '__main__':
    main()
