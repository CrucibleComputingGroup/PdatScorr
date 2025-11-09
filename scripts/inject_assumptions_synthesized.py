#!/usr/bin/env python3
"""
Inject instruction assumptions into synthesized (gate-level) Verilog modules.

For synthesized modules, we create a wrapper that:
1. Instantiates the original synthesized module
2. Adds assumption statements referencing the appropriate signals
3. Extracts the instruction from the packed input vector
"""

import argparse
import re


def find_instruction_signal(module_content):
    """Find the instruction signal in the synthesized module.

    For CVA6 id_stage, the instruction is in fetch_entry_i[301:270]

    Returns:
        tuple: (signal_name, bit_range) or None if not found
    """
    # Look for compressed decoder instantiation
    # compressed_decoder(.instr_i(fetch_entry_i[301:270]), ...)
    pattern = r'compressed_decoder.*?\.instr_i\(([^\)]+)\)'
    match = re.search(pattern, module_content, re.DOTALL)

    if match:
        signal = match.group(1).strip()
        return signal

    # Fallback: look for instruction_rvc wire
    pattern = r'wire\s+\[31:0\]\s+instruction_rvc'
    if re.search(pattern, module_content):
        # Try to find what feeds it
        pattern = r'\.instr_o\(instruction_rvc\).*?\.instr_i\(([^\)]+)\)'
        match = re.search(pattern, module_content, re.DOTALL)
        if match:
            return match.group(1).strip()

    return None


def create_wrapper_module(original_module_file, assumptions_code, output_file):
    """Create a wrapper module that adds assumptions to a synthesized module.

    Args:
        original_module_file: Path to the original synthesized module
        assumptions_code: The assumption code to inject
        output_file: Path to write the wrapper module
    """
    with open(original_module_file, 'r') as f:
        content = f.read()

    # Extract module name and ports
    module_match = re.search(r'module\s+(\w+)\s*\((.*?)\);', content, re.DOTALL)
    if not module_match:
        raise ValueError("Could not find module declaration")

    original_module_name = module_match.group(1)
    ports_text = module_match.group(2)

    # Find instruction signal in the module
    instr_signal = find_instruction_signal(content)

    if not instr_signal:
        print("Warning: Could not automatically find instruction signal")
        print("Using default: fetch_entry_i[301:270]")
        instr_signal = "fetch_entry_i[301:270]"

    print(f"Found instruction signal: {instr_signal}")

    # Create wrapper module name
    wrapper_module_name = original_module_name.replace("__", "_wrapped__")

    # Build wrapper module
    wrapper = f"""// Auto-generated wrapper for {original_module_name}
// Adds instruction constraints to synthesized module

module {wrapper_module_name} ({ports_text});

  // Extract instruction signal for assumptions
  wire [31:0] instr_rdata_i = {instr_signal};

{assumptions_code}

  // Instantiate original synthesized module
  {original_module_name} original_instance (
"""

    # Add port connections
    # Parse ports and create pass-through connections
    ports_list = []
    for port in ports_text.split(','):
        port = port.strip()
        if port:
            # Extract port name (last word before optional array)
            port_match = re.search(r'(\w+)\s*(?:\[.*?\])?\s*$', port)
            if port_match:
                port_name = port_match.group(1)
                ports_list.append(port_name)

    # Generate port connections
    for i, port_name in enumerate(ports_list):
        suffix = ',' if i < len(ports_list) - 1 else ''
        wrapper += f"    .{port_name}({port_name}){suffix}\n"

    wrapper += "  );\n\nendmodule\n"

    # Write wrapper to output
    with open(output_file, 'w') as f:
        f.write(wrapper)

    print(f"Created wrapper module: {wrapper_module_name}")
    return wrapper_module_name


def inject_assumptions_inline(module_file, assumptions_code, output_file):
    """Inject assumptions directly before endmodule (simpler approach).

    This works even for synthesized Verilog if we can map the instruction signal.
    """
    with open(module_file, 'r') as f:
        content = f.read()

    # Find instruction signal
    instr_signal = find_instruction_signal(content)

    if not instr_signal:
        print("Warning: Could not find instruction signal, using fetch_entry_i[301:270]")
        instr_signal = "fetch_entry_i[301:270]"

    print(f"Injecting assumptions using instruction signal: {instr_signal}")

    # Adapt assumptions code to use the correct signal name
    # For synthesized cores, we need to create an intermediate wire first
    # Then replace references to instr_rdata_i

    # Create intermediate wire declaration
    wire_decl = f"  // Extract instruction from packed input\n"
    wire_decl += f"  wire [31:0] instr_rdata_i_extracted;\n"
    wire_decl += f"  assign instr_rdata_i_extracted = {instr_signal};\n\n"

    # Replace 'instr_rdata_i' with the intermediate wire name
    adapted_assumptions = assumptions_code.replace('instr_rdata_i', 'instr_rdata_i_extracted')

    # Convert SystemVerilog to pure Verilog syntax for Synlig
    # Keep 'assume' as-is - Synlig supports it in always blocks
    # No need to convert to $assume
    import re

    # Now replace the field extraction wires to use the intermediate wire
    # This avoids chained indexing like fetch_entry_i[301:270][11:7]
    adapted_assumptions = wire_decl + adapted_assumptions

    # Find the last endmodule
    last_endmodule = content.rfind('endmodule')

    if last_endmodule == -1:
        raise ValueError("Could not find 'endmodule' in file")

    # Insert before endmodule
    modified_content = (
        content[:last_endmodule] +
        "\n  // ========================================\n" +
        "  // Injected instruction constraints\n" +
        "  // ========================================\n" +
        adapted_assumptions +
        "\n" +
        content[last_endmodule:]
    )

    with open(output_file, 'w') as f:
        f.write(modified_content)

    print(f"Successfully injected assumptions into {output_file}")


def main():
    parser = argparse.ArgumentParser(
        description='Inject assumptions into synthesized Verilog modules'
    )
    parser.add_argument('module_file', help='Path to synthesized module file')
    parser.add_argument('output_file', help='Output file path')
    parser.add_argument('--assumptions-file', required=True,
                       help='File containing assumptions code')
    parser.add_argument('--wrapper', action='store_true',
                       help='Create wrapper module instead of inline injection')

    args = parser.parse_args()

    # Load assumptions
    with open(args.assumptions_file, 'r') as f:
        assumptions_code = f.read()

    print(f"Processing {args.module_file}...")

    try:
        if args.wrapper:
            create_wrapper_module(args.module_file, assumptions_code, args.output_file)
        else:
            inject_assumptions_inline(args.module_file, assumptions_code, args.output_file)

        print(f"Successfully created {args.output_file}")
        return 0

    except Exception as e:
        print(f"Error: {e}")
        import traceback
        traceback.print_exc()
        return 1


if __name__ == '__main__':
    exit(main())
