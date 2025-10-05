#!/usr/bin/env python3
"""
Generate a SystemVerilog assertion module from instruction DSL.

This script:
1. Parses the DSL file containing instruction rules
2. Converts high-level instruction rules to pattern/mask pairs
3. Generates a SystemVerilog module with assertions
"""

import sys
import argparse
from typing import List, Tuple
from instruction_dsl_parser import parse_dsl, InstructionRule, PatternRule, FieldConstraint
from riscv_encodings import (
    get_instruction_encoding, parse_register, set_field, create_field_mask
)

def instruction_rule_to_pattern(rule: InstructionRule) -> List[Tuple[int, int, str]]:
    """
    Convert an InstructionRule to one or more (pattern, mask, description) tuples.

    Returns a list because some rules with wildcards might expand to multiple patterns.
    """
    # Get the base encoding for this instruction
    encoding = get_instruction_encoding(rule.name)
    if not encoding:
        print(f"Warning: Unknown instruction '{rule.name}' at line {rule.line}, skipping")
        return []

    # Start with the base pattern and mask
    pattern = encoding.base_pattern
    mask = encoding.base_mask

    # Apply field constraints
    for constraint in rule.constraints:
        field_name = constraint.field_name
        field_value = constraint.field_value

        # Check if this field exists in the instruction format
        if field_name not in encoding.fields:
            print(f"Warning: Field '{field_name}' not valid for {rule.name} at line {rule.line}")
            continue

        field_pos, field_width = encoding.fields[field_name]

        # Handle wildcards - don't add to mask
        if field_value in ('*', 'x', '_'):
            # Wildcard means we don't care about this field
            # Remove this field from the mask (set those bits to 0)
            field_mask = create_field_mask(field_pos, field_width)
            mask = mask & ~field_mask
            continue

        # Handle register names
        if field_name in ('rd', 'rs1', 'rs2'):
            reg_num = parse_register(field_value)
            if reg_num is None:
                # Try to parse as number
                if isinstance(field_value, int):
                    reg_num = field_value
                else:
                    print(f"Warning: Invalid register '{field_value}' at line {rule.line}")
                    continue
            field_value = reg_num

        # Handle numeric values
        if isinstance(field_value, str):
            # Try to parse as hex/binary/decimal
            try:
                if field_value.startswith('0x'):
                    field_value = int(field_value, 16)
                elif field_value.startswith('0b'):
                    field_value = int(field_value, 2)
                else:
                    field_value = int(field_value)
            except ValueError:
                print(f"Warning: Cannot parse field value '{field_value}' at line {rule.line}")
                continue

        # Set the field in the pattern and add to mask
        pattern = set_field(pattern, field_pos, field_width, field_value)
        mask = mask | create_field_mask(field_pos, field_width)

    # Create description
    desc = f"{rule.name}"
    if rule.constraints:
        constraint_strs = [f"{c.field_name}={c.field_value}" for c in rule.constraints]
        desc += " { " + ", ".join(constraint_strs) + " }"

    return [(pattern, mask, desc)]

def generate_sv_module(patterns: List[Tuple[int, int, str]], module_name: str = "instr_outlawed_checker") -> str:
    """Generate SystemVerilog module with pattern-matching assertions."""

    sv_code = f"""// Auto-generated instruction pattern checker module
// This module checks that certain instruction patterns are never present in the pipeline

module {module_name} (
  input logic        clk_i,
  input logic        rst_ni,
  input logic        instr_valid_i,
  input logic [31:0] instr_rdata_i,
  input logic        instr_is_compressed_i
);

"""

    # Group by width (assume all 32-bit for now, can add 16-bit later)
    patterns_32 = [(p, m, d) for p, m, d in patterns if m <= 0xFFFFFFFF]

    if patterns_32:
        sv_code += "  // 32-bit outlawed instruction patterns\n"
        for i, (pattern, mask, desc) in enumerate(patterns_32):
            sv_code += f"  // {desc}\n"
            sv_code += f"  // Pattern: 0x{pattern:08x}, Mask: 0x{mask:08x}\n"
            sv_code += f"  always @(posedge clk_i) begin\n"
            sv_code += f"    if (rst_ni && instr_valid_i && !instr_is_compressed_i) begin\n"
            sv_code += f"      assert ((instr_rdata_i & 32'h{mask:08x}) != 32'h{pattern:08x}) else\n"
            sv_code += f"        $error(\"Outlawed instruction: {desc} - instr=0x%08x\", instr_rdata_i);\n"
            sv_code += f"    end\n"
            sv_code += f"  end\n\n"

    if not patterns_32:
        sv_code += "  // No outlawed instruction patterns specified\n\n"

    sv_code += "endmodule\n"

    return sv_code

def generate_bind_file(module_name: str) -> str:
    """Generate a bind file for the checker module."""
    bind_code = f"""// Auto-generated bind file for {module_name}
// This file binds the instruction checker to the Ibex ID stage

bind ibex_core.id_stage_i {module_name} checker_inst (
  .clk_i                  (clk_i),
  .rst_ni                 (rst_ni),
  .instr_valid_i          (instr_valid_i),
  .instr_rdata_i          (instr_rdata_i),
  .instr_is_compressed_i  (instr_is_compressed_i)
);
"""
    return bind_code

def main():
    parser = argparse.ArgumentParser(
        description='Generate SystemVerilog assertion module from instruction DSL'
    )
    parser.add_argument('input_file', help='DSL file containing instruction rules')
    parser.add_argument('output_file', help='Output SystemVerilog file')
    parser.add_argument('-m', '--module-name', default='instr_outlawed_checker',
                       help='Name of generated module (default: instr_outlawed_checker)')
    parser.add_argument('-b', '--bind-file',
                       help='Output bind file (default: <output_file_base>_bind.sv)')

    args = parser.parse_args()

    # Determine bind file name
    if args.bind_file:
        bind_file = args.bind_file
    else:
        # Default: replace .sv with _bind.sv
        if args.output_file.endswith('.sv'):
            bind_file = args.output_file[:-3] + '_bind.sv'
        else:
            bind_file = args.output_file + '_bind.sv'

    # Read input file
    with open(args.input_file, 'r') as f:
        dsl_text = f.read()

    # Parse DSL
    print(f"Parsing {args.input_file}...")
    try:
        ast = parse_dsl(dsl_text)
    except SyntaxError as e:
        print(f"Syntax error: {e}")
        sys.exit(1)

    print(f"Found {len(ast.rules)} rules")

    # Convert to patterns
    patterns = []
    for rule in ast.rules:
        if isinstance(rule, InstructionRule):
            rule_patterns = instruction_rule_to_pattern(rule)
            patterns.extend(rule_patterns)
        elif isinstance(rule, PatternRule):
            desc = rule.description if rule.description else f"Pattern at line {rule.line}"
            patterns.append((rule.pattern, rule.mask, desc))

    print(f"Generated {len(patterns)} patterns")

    # Generate SystemVerilog
    print(f"Generating SystemVerilog module '{args.module_name}'...")
    sv_code = generate_sv_module(patterns, args.module_name)

    # Write checker module
    with open(args.output_file, 'w') as f:
        f.write(sv_code)
    print(f"Successfully wrote {args.output_file}")

    # Generate and write bind file
    bind_code = generate_bind_file(args.module_name)
    with open(bind_file, 'w') as f:
        f.write(bind_code)
    print(f"Successfully wrote {bind_file}")

if __name__ == '__main__':
    main()
