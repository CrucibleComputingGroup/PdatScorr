#!/usr/bin/env python3
"""
Apply ODC optimizations: Create optimized RTL with constant tie-offs

Reads ODC analysis report and generates RTL with confirmed ODC bits
tied to constants. This can then be re-synthesized to measure area improvement.
"""

import sys
import json
import argparse
from pathlib import Path
from typing import List, Dict

# Add project root to path
PROJECT_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(PROJECT_ROOT))


def read_odc_report(report_json: Path) -> List[Dict]:
    """
    Read ODC report and extract confirmed ODCs.
    
    Returns:
        List of ODC bits with their constant values
    """
    with open(report_json) as f:
        report = json.load(f)
    
    confirmed_odcs = []
    for result in report["results"]:
        if result["is_odc"]:
            confirmed_odcs.append({
                "field": result["field"],
                "bit_position": result["bit_position"],
                "constant_value": result["expected_constant_value"],
                "instruction": result.get("instruction")
            })
    
    return confirmed_odcs


def apply_shift_amt_tie_offs(source_file: Path, output_file: Path,
                             odc_bits: List[Dict]) -> bool:
    """
    Apply constant tie-offs for shift_amt bits.

    Uses a hybrid approach: Original logic computes shift_amt_original,
    then we selectively override ODC bits while keeping non-ODC bits.

    Args:
        source_file: Original ibex_alu.sv
        output_file: Optimized ibex_alu.sv with tie-offs
        odc_bits: List of ODC bits to tie off

    Returns:
        True if successful
    """
    with open(source_file) as f:
        content = f.read()

    lines = content.split('\n')

    # Find injection point (after shift_amt always_comb block)
    injection_line = None
    for i, line in enumerate(lines):
        if '// single-bit mode: shift' in line:
            injection_line = i
            break

    if injection_line is None:
        raise ValueError("Could not find injection point in ibex_alu.sv")

    # Rename shift_amt to shift_amt_original in the always_comb block
    # Search backwards to find the always_comb block
    always_comb_start = None
    always_comb_end = None

    for i in range(injection_line - 1, max(0, injection_line - 20), -1):
        if lines[i].strip() == 'end':
            for j in range(i - 1, max(0, i - 15), -1):
                if 'always_comb begin' in lines[j] and 'shift_amt' in ''.join(lines[j:i]):
                    always_comb_start = j
                    always_comb_end = i
                    break
            if always_comb_start:
                break

    if always_comb_start and always_comb_end:
        print(f"  Renaming shift_amt → shift_amt_original in always_comb (lines {always_comb_start+1}-{always_comb_end+1})")
        # Rename shift_amt to shift_amt_original in assignments
        for i in range(always_comb_start, always_comb_end + 1):
            # Replace shift_amt[4:0] = with shift_amt_original[4:0] =
            lines[i] = lines[i].replace('shift_amt[4:0] =', 'shift_amt_original[4:0] =')

    # Generate ODC optimization code with selective bit override
    odc_bit_map = {odc['bit_position']: odc['constant_value'] for odc in odc_bits}

    tie_off_code = [
        "",
        "  // ========================================",
        "  // ODC OPTIMIZATION: Selective bit override",
        "  // Proven ODC bits tied to constants, others use computed value",
        "  // ========================================",
        "  logic [4:0] shift_amt_original;  // Original computed value",
        "",
    ]

    # Generate bit-by-bit assignment
    tie_off_code.append("  // Final shift_amt: ODC bits forced, others from original logic")
    for bit in range(5):
        if bit in odc_bit_map:
            val = odc_bit_map[bit]
            tie_off_code.append(f"  assign shift_amt[{bit}] = 1'b{val};  // ODC: constant")
        else:
            tie_off_code.append(f"  assign shift_amt[{bit}] = shift_amt_original[{bit}];  // Non-ODC: from logic")

    tie_off_code.append("")

    # Insert optimization code
    lines.insert(injection_line, '\n'.join(tie_off_code))
    
    # Write optimized file
    output_file.parent.mkdir(parents=True, exist_ok=True)
    with open(output_file, 'w') as f:
        f.write('\n'.join(lines))
    
    return True


def main():
    parser = argparse.ArgumentParser(
        description="Apply ODC optimizations to RTL based on analysis results"
    )
    parser.add_argument("odc_report", type=Path, 
                       help="ODC report JSON file (e.g., odc_analysis/odc_report.json)")
    parser.add_argument("--rtl-dir", type=Path, required=True,
                       help="Core RTL directory (e.g., ../PdatCoreSim/cores/ibex/rtl)")
    parser.add_argument("--output-dir", type=Path, required=True,
                       help="Output directory for optimized RTL")
    parser.add_argument("--field", default="shamt",
                       help="Field to optimize (default: shamt)")
    
    args = parser.parse_args()
    
    if not args.odc_report.exists():
        print(f"ERROR: ODC report not found: {args.odc_report}")
        return 1
    
    # Read ODC report
    print(f"Reading ODC report: {args.odc_report}")
    confirmed_odcs = read_odc_report(args.odc_report)
    
    if not confirmed_odcs:
        print("No confirmed ODCs found in report")
        return 0
    
    print(f"Found {len(confirmed_odcs)} confirmed ODCs:")
    for odc in confirmed_odcs:
        print(f"  {odc['field']}[{odc['bit_position']}] = {odc['constant_value']}")
    print()
    
    # Filter by field
    field_odcs = [odc for odc in confirmed_odcs if odc['field'] == args.field]
    
    if not field_odcs:
        print(f"No ODCs found for field '{args.field}'")
        return 0
    
    # Apply optimizations based on field
    if args.field == "shamt":
        source_file = args.rtl_dir / "ibex_alu.sv"
        output_file = args.output_dir / "ibex_alu_optimized.sv"
        
        print(f"Applying {len(field_odcs)} tie-offs to {source_file.name}...")
        success = apply_shift_amt_tie_offs(source_file, output_file, field_odcs)
        
        if success:
            print(f"Created optimized RTL: {output_file}")
            print()
            print("Next steps:")
            print("  1. Re-synthesize with optimized RTL")
            print("  2. Compare area/power with baseline")
            return 0
    else:
        print(f"ERROR: Optimization for field '{args.field}' not implemented yet")
        return 1


if __name__ == "__main__":
    sys.exit(main())
