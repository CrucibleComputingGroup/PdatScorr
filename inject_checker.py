#!/usr/bin/env python3
"""
Inject instruction checker instantiation into ibex_id_stage.sv
"""

import argparse
import re

def inject_checker(id_stage_file: str, output_file: str, checker_module: str):
    """Read ibex_id_stage.sv and inject checker instantiation before endmodule."""

    with open(id_stage_file, 'r') as f:
        content = f.read()

    # Find the last endmodule
    # Add the checker instantiation right before it
    checker_inst = f"""
  // Instruction outlawed checker (auto-generated)
  {checker_module} u_instr_checker (
    .clk_i                  (clk_i),
    .rst_ni                 (rst_ni),
    .instr_valid_i          (instr_valid_i),
    .instr_rdata_i          (instr_rdata_i),
    .instr_is_compressed_i  (instr_is_compressed_i)
  );

"""

    # Find the position of the last endmodule
    last_endmodule = content.rfind('endmodule')

    if last_endmodule == -1:
        raise ValueError("Could not find 'endmodule' in file")

    # Insert the checker before endmodule
    modified_content = content[:last_endmodule] + checker_inst + content[last_endmodule:]

    # Write to output file
    with open(output_file, 'w') as f:
        f.write(modified_content)

    return True

def main():
    parser = argparse.ArgumentParser(
        description='Inject instruction checker into ibex_id_stage.sv'
    )
    parser.add_argument('id_stage_file', help='Path to original ibex_id_stage.sv')
    parser.add_argument('output_file', help='Output modified file')
    parser.add_argument('-m', '--checker-module', default='instr_outlawed_checker',
                       help='Name of checker module (default: instr_outlawed_checker)')

    args = parser.parse_args()

    print(f"Injecting {args.checker_module} into {args.id_stage_file}...")

    try:
        inject_checker(args.id_stage_file, args.output_file, args.checker_module)
        print(f"Successfully created {args.output_file}")
    except Exception as e:
        print(f"Error: {e}")
        return 1

    return 0

if __name__ == '__main__':
    exit(main())
