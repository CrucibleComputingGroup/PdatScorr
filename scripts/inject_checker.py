#!/usr/bin/env python3
"""
Inject instruction assumptions directly into ibex_id_stage.sv
"""

import argparse
import re

def inject_assumptions(id_stage_file: str, output_file: str, assumptions_code: str):
    """Read ibex_id_stage.sv and inject assumption code before endmodule."""

    with open(id_stage_file, 'r') as f:
        content = f.read()

    # Find the position of the last endmodule
    last_endmodule = content.rfind('endmodule')

    if last_endmodule == -1:
        raise ValueError("Could not find 'endmodule' in file")

    # Insert the assumptions before endmodule
    modified_content = content[:last_endmodule] + assumptions_code + content[last_endmodule:]

    # Write to output file
    with open(output_file, 'w') as f:
        f.write(modified_content)

    return True

def generate_assumptions_from_patterns(patterns, module_name="ibex_id_stage"):
    """Generate assumption code directly (no separate module)."""

    code = "\n  // ========================================\n"
    code += "  // Auto-generated instruction constraints\n"
    code += "  // ========================================\n\n"

    if not patterns:
        code += "  // No outlawed instruction patterns specified\n\n"
        return code

    # Check if we have MUL/DIV instructions
    has_mul = any('MUL' in desc for _, _, desc in patterns)
    has_div = any('DIV' in desc or 'REM' in desc for _, _, desc in patterns)

    code += "  // Instruction encoding constraints\n"
    for i, (pattern, mask, desc) in enumerate(patterns):
        code += f"  // {desc}: Pattern=0x{pattern:08x}, Mask=0x{mask:08x}\n"
        code += f"  always_comb begin\n"
        code += f"    if (rst_ni && instr_valid_i && !instr_is_compressed_i) begin\n"
        code += f"      assume ((instr_rdata_i & 32'h{mask:08x}) != 32'h{pattern:08x});\n"
        code += f"    end\n"
        code += f"  end\n\n"

    # Direct decoder output constraints removed for testing
    # MUL/DIV will only be constrained through pattern matching above

    return code

def main():
    parser = argparse.ArgumentParser(
        description='Inject instruction assumptions into ibex_id_stage.sv'
    )
    parser.add_argument('id_stage_file', help='Path to original ibex_id_stage.sv')
    parser.add_argument('output_file', help='Output modified file')
    parser.add_argument('--assumptions-file', help='File containing assumptions code to inject')

    args = parser.parse_args()

    print(f"Injecting assumptions into {args.id_stage_file}...")

    try:
        if args.assumptions_file:
            with open(args.assumptions_file, 'r') as f:
                assumptions_code = f.read()
        else:
            assumptions_code = "\n  // No assumptions injected\n\n"

        inject_assumptions(args.id_stage_file, args.output_file, assumptions_code)
        print(f"Successfully created {args.output_file}")
    except Exception as e:
        print(f"Error: {e}")
        return 1

    return 0

if __name__ == '__main__':
    exit(main())
