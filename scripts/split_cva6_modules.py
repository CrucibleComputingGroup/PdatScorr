#!/usr/bin/env python3
"""
Split the monolithic synthesized CVA6 Verilog file into separate module files.

This allows the injection scripts to work with individual modules.
"""

import re
import sys
from pathlib import Path


def split_verilog_modules(input_file, output_dir):
    """Split a monolithic Verilog file into individual module files.

    Args:
        input_file: Path to the monolithic Verilog file
        output_dir: Directory to write individual module files
    """
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    # Track which modules we want to extract separately
    # Other modules will go into a "common" file
    key_modules = {
        'id_stage': re.compile(r'^module id_stage__\d+'),
        'decoder': re.compile(r'^module decoder__\d+'),
        'cva6': re.compile(r'^module cva6\s*\('),
    }

    current_module = None
    current_module_name = None
    current_lines = []
    common_modules = []
    extracted_modules = {}

    print(f"Reading {input_file}...")
    with open(input_file, 'r') as f:
        for line_num, line in enumerate(f, 1):
            # Check if this is a module declaration
            if line.strip().startswith('module '):
                if current_module is not None:
                    print(f"Warning: Found nested module at line {line_num}")

                # Check if this is a key module we want to extract
                matched_key = None
                for key, pattern in key_modules.items():
                    if pattern.match(line):
                        matched_key = key
                        break

                if matched_key:
                    current_module = matched_key
                    current_module_name = line.split()[1].split('(')[0].strip()
                    current_lines = [line]
                    print(f"  Found {matched_key} module: {current_module_name} (line {line_num})")
                else:
                    # This is a common module
                    current_module = 'common'
                    current_lines = [line]

            elif line.strip() == 'endmodule':
                current_lines.append(line)

                # Save the completed module
                if current_module == 'common':
                    common_modules.extend(current_lines)
                    common_modules.append('\n')  # Add blank line between modules
                else:
                    if current_module not in extracted_modules:
                        extracted_modules[current_module] = []
                    extracted_modules[current_module].extend(current_lines)

                # Reset state
                current_module = None
                current_module_name = None
                current_lines = []

            else:
                # Continue accumulating lines for current module
                if current_module is not None:
                    current_lines.append(line)

    # Write out the extracted modules
    print(f"\nWriting extracted modules to {output_dir}/...")

    # Write key modules to their own files
    for module_name, lines in extracted_modules.items():
        output_file = output_dir / f"{module_name}.v"
        with open(output_file, 'w') as f:
            f.writelines(lines)
        print(f"  Wrote {module_name}.v ({len(lines)} lines)")

    # Write common modules to a single file
    if common_modules:
        output_file = output_dir / "cva6_common_modules.v"
        with open(output_file, 'w') as f:
            f.writelines(common_modules)
        print(f"  Wrote cva6_common_modules.v ({len(common_modules)} lines)")

    print("\nDone!")
    print(f"Total files created: {len(extracted_modules) + (1 if common_modules else 0)}")


def main():
    if len(sys.argv) != 3:
        print("Usage: split_cva6_modules.py <input_verilog> <output_dir>")
        print("\nExample:")
        print("  split_cva6_modules.py cv64a6_synth.v cva6_split/")
        return 1

    input_file = sys.argv[1]
    output_dir = sys.argv[2]

    if not Path(input_file).exists():
        print(f"Error: Input file not found: {input_file}")
        return 1

    split_verilog_modules(input_file, output_dir)
    return 0


if __name__ == '__main__':
    sys.exit(main())
