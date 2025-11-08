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


def apply_register_field_tie_offs_combined(source_file: Path, output_file: Path,
                                           odc_bits: List[Dict]) -> bool:
    """
    Apply constant tie-offs for unused registers in the register file.

    Modifies ibex_register_file_ff.sv to eliminate storage for unused registers.
    When register address bits are proven to be ODCs (e.g., rd[4:2]=0 for x0-x3),
    we can eliminate the physical register storage for x4-x31.

    Args:
        source_file: Original ibex_register_file_ff.sv (or equivalent)
        output_file: Optimized register file with unused registers eliminated
        odc_bits: List of all register field ODC bits to tie off

    Returns:
        True if successful
    """
    # Determine which registers are unused based on ODC bits
    # If rd[4]=0, rs1[4]=0, rs2[4]=0, then registers x16-x31 are unused
    # If rd[3]=0, rs1[3]=0, rs2[3]=0 additionally, then x8-x31 are unused, etc.

    # Find maximum usable register based on constant bits
    # Group ODCs by bit position
    odc_bits_by_pos = {}
    for odc in odc_bits:
        pos = odc['bit_position']
        if pos not in odc_bits_by_pos:
            odc_bits_by_pos[pos] = []
        odc_bits_by_pos[pos].append(odc)

    # For a bit position to be truly constant, ALL register fields (rd, rs1, rs2)
    # must have it as an ODC
    constant_bit_positions = []
    for pos in range(5):  # 5-bit register addresses
        # Check if all three fields have this bit as ODC with value 0
        fields_with_odc = set()
        all_zero = True
        for odc in odc_bits:
            if odc['bit_position'] == pos:
                fields_with_odc.add(odc['field'])
                if odc['constant_value'] != 0:
                    all_zero = False

        # Must have all three fields (rd, rs1, rs2) with this bit = 0
        if fields_with_odc >= {'rd', 'rs1', 'rs2'} and all_zero:
            constant_bit_positions.append(pos)

    if not constant_bit_positions:
        print("  No consistent register address constants across all fields")
        return False

    # Calculate max usable register
    # If bits [4:2] are all 0, then max register is 2^2 - 1 = 3
    max_usable_reg = 0
    for bit_pos in range(5):
        if bit_pos not in constant_bit_positions:
            max_usable_reg |= (1 << bit_pos)

    num_registers = max_usable_reg + 1
    print(f"  Max usable register: x{max_usable_reg} (need {num_registers} registers)")

    # Read source file
    print(f"  Reading: {source_file}")
    with open(source_file) as f:
        content = f.read()

    lines = content.split('\n')
    print(f"  File has {len(lines)} lines")

    # Step 1: Add parameter for reduced register count
    # Find the end of port declarations (after the );)
    for i, line in enumerate(lines):
        if ');' in line and i > 10 and 'module' not in line:  # End of port list
            # Insert after port declarations
            lines.insert(i+1, "")
            lines.insert(i+2, f"  // ODC OPTIMIZATION: Reduce register file size")
            lines.insert(i+3, f"  localparam int unsigned NUM_WORDS_ODC = {num_registers};")
            print(f"  Added NUM_WORDS_ODC parameter = {num_registers} after line {i+1}")
            break

    # Step 2: Change array declaration size
    for i, line in enumerate(lines):
        if 'logic' in line and 'rf_reg' in line and '[NUM_WORDS]' in line:
            print(f"  Found rf_reg array at line {i+1}: {line.strip()[:60]}")
            # Change NUM_WORDS to NUM_WORDS_ODC
            lines[i] = line.replace('[NUM_WORDS]', '[NUM_WORDS_ODC]')
            print(f"  Changed to: {lines[i].strip()[:60]}")

    # Step 3: Find the register generation loop
    # Looking for: for (genvar i = 1; i < NUM_WORDS; i++) begin : g_rf_flops
    gen_loop_start = None
    gen_loop_end = None

    for i, line in enumerate(lines):
        if 'g_rf_flops' in line:
            print(f"  Found 'g_rf_flops' at line {i+1}: {line.strip()[:80]}")
        if 'for (genvar i = 1' in line and 'NUM_WORDS' in line and 'g_rf_flops' in line:
            print(f"  Matched generation loop at line {i+1}")
            gen_loop_start = i
            # Find matching end
            depth = 0
            for j in range(i, len(lines)):
                if 'begin' in lines[j]:
                    depth += 1
                # Match 'end' as a standalone keyword (with optional semicolon/comment)
                stripped = lines[j].strip()
                if stripped == 'end' or stripped.startswith('end ') or stripped.startswith('end;') or stripped.startswith('end//'):
                    depth -= 1
                    if depth == 0:
                        gen_loop_end = j
                        print(f"  Found loop end at line {j+1}: {lines[j].strip()[:40]}")
                        break
            if gen_loop_end is None:
                print(f"  WARNING: Could not find matching 'end' for loop")
            break

    if gen_loop_start is None or gen_loop_end is None:
        print(f"  ERROR: gen_loop_start={gen_loop_start}, gen_loop_end={gen_loop_end}")
        raise ValueError(f"Could not find register generation loop in {source_file.name}")

    print(f"  Found register generation loop at lines {gen_loop_start+1}-{gen_loop_end+1}")

    # Extract the loop body
    loop_body = lines[gen_loop_start+1:gen_loop_end]

    # Create modified loop with reduced iteration range to match reduced array
    # Change: for (genvar i = 1; i < NUM_WORDS; i++)
    # To:     for (genvar i = 1; i < NUM_WORDS_ODC; i++)
    modified_loop_header = lines[gen_loop_start].replace('i < NUM_WORDS', f'i < NUM_WORDS_ODC')

    modified_loop = [
        f"  // ODC OPTIMIZATION: Only generate registers 1..{max_usable_reg}",
        modified_loop_header,
    ]

    # Keep the original loop body unchanged
    modified_loop.extend(loop_body)

    modified_loop.append("  end  // g_rf_flops")

    # Replace the loop
    lines[gen_loop_start:gen_loop_end+1] = modified_loop

    # Step 4: Modify read logic to handle reduced array
    # Find: assign rdata_a_o = rf_reg[raddr_a_i];
    # Change to: assign rdata_a_o = (raddr_a_i < NUM_WORDS_ODC) ? rf_reg[raddr_a_i] : '0;
    for i, line in enumerate(lines):
        if 'assign rdata_a_o' in line and 'rf_reg[raddr_a_i]' in line:
            print(f"  Modifying rdata_a read at line {i+1}")
            lines[i] = f"  assign rdata_a_o = (raddr_a_i < NUM_WORDS_ODC) ? rf_reg[raddr_a_i] : '0;  // ODC: Clamp to valid range"

        if 'assign rdata_b_o' in line and 'rf_reg[raddr_b_i]' in line:
            print(f"  Modifying rdata_b read at line {i+1}")
            lines[i] = f"  assign rdata_b_o = (raddr_b_i < NUM_WORDS_ODC) ? rf_reg[raddr_b_i] : '0;  // ODC: Clamp to valid range"

    # Write optimized content
    output_file.parent.mkdir(parents=True, exist_ok=True)
    with open(output_file, 'w') as f:
        f.write('\n'.join(lines))

    print(f"  Modified register file: {num_registers} active registers, {32 - num_registers} tied to 0")

    return True


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
    parser.add_argument("--config", type=Path, default=Path("configs/ibex.yaml"),
                       help="Core configuration file (default: configs/ibex.yaml)")
    parser.add_argument("--field", default="all",
                       help="Field to optimize: 'all' for all fields (shamt, rd, rs1, rs2, imm), or specific field name (default: all)")

    args = parser.parse_args()

    if not args.odc_report.exists():
        print(f"ERROR: ODC report not found: {args.odc_report}")
        return 1

    # Load config to get core-specific file names
    sys.path.insert(0, str(PROJECT_ROOT / "scripts"))
    from config_loader import ConfigLoader

    try:
        config = ConfigLoader.load_config(str(args.config))
        print(f"Using config for core: {config.core_name}")
    except Exception as e:
        print(f"ERROR: Failed to load config: {e}")
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

    # Group ODCs by field
    odcs_by_field = {}
    for odc in confirmed_odcs:
        field = odc['field']
        if field not in odcs_by_field:
            odcs_by_field[field] = []
        odcs_by_field[field].append(odc)

    # Filter by field if specified
    if args.field != "all":
        odcs_by_field = {args.field: odcs_by_field.get(args.field, [])}

    # Apply optimizations for each field
    # Group register fields together (rd, rs1, rs2 all go into one id_stage file)
    register_fields = ["rd", "rs1", "rs2"]
    register_odcs = []
    other_fields = {}

    for field, field_odcs in odcs_by_field.items():
        if field in register_fields:
            register_odcs.extend(field_odcs)
        else:
            other_fields[field] = field_odcs

    success_count = 0

    # Apply register field ODCs (modify register file)
    if register_odcs:
        print(f"Processing register fields (rd/rs1/rs2): {len(register_odcs)} total ODCs")

        # Target the register file for optimization
        # Use config to find register file from source_files list
        source_file = None

        # Search config source_files for register file
        for src_file in config.synthesis.source_files:
            if "regfile" in src_file.lower() or "register_file" in src_file.lower():
                # Found it - construct full path
                source_file = Path(config.synthesis.core_root_resolved) / src_file
                if source_file.exists():
                    break
                source_file = None  # Reset if file doesn't exist

        # Fallback: try common patterns in rtl_dir
        if source_file is None:
            register_file_candidates = [
                "ibex_register_file_ff.sv",
                "register_file.sv",
                "regfile.sv",
                "rf.sv"
            ]

            for candidate in register_file_candidates:
                candidate_path = args.rtl_dir / candidate
                if candidate_path.exists():
                    source_file = candidate_path
                    break

        if source_file is None:
            print(f"  ERROR: Could not find register file")
            print(f"  Searched in config source_files and {args.rtl_dir}")
        else:
            # Generate output filename
            output_filename = f"{source_file.stem}_optimized.sv"
            output_file = args.output_dir / output_filename

            print(f"  Modifying register file: {source_file.name}")
            success = apply_register_field_tie_offs_combined(source_file, output_file, register_odcs)

            if success:
                print(f"  ✓ Created: {output_file.name}")
                success_count += 1

    # Apply other field optimizations
    for field, field_odcs in other_fields.items():
        if not field_odcs:
            continue

        print(f"Processing field '{field}' ({len(field_odcs)} ODCs)...")

        if field == "shamt":
            # Get ALU source file from config (odc_error injection point)
            alu_injection = config.get_injection("odc_error")
            if not alu_injection:
                print(f"  ERROR: No odc_error injection point found in config for field '{field}'")
                continue

            source_file = args.rtl_dir / Path(alu_injection.source_file).name
            output_filename = f"{Path(alu_injection.source_file).stem}_optimized.sv"
            output_file = args.output_dir / output_filename

            print(f"  Applying {len(field_odcs)} tie-offs to {source_file.name}...")
            success = apply_shift_amt_tie_offs(source_file, output_file, field_odcs)

            if success:
                print(f"  ✓ Created: {output_file.name}")
                success_count += 1
        else:
            print(f"  WARNING: Optimization for field '{field}' not implemented yet")

    if success_count > 0:
        print()
        print(f"Successfully optimized {success_count} fields")
        print("Next steps:")
        print("  1. Re-synthesize with optimized RTL")
        print("  2. Compare area/power with baseline")
        return 0
    else:
        print("No optimizations applied")
        return 1


if __name__ == "__main__":
    sys.exit(main())
