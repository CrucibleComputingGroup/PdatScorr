#!/usr/bin/env python3
"""
Inject cache timing constraints into ibex_core.sv

This script injects timing constraint code (counters and assumptions) into ibex_core.sv
at the appropriate location where core-level signals are visible.
"""

import argparse
import sys
from pathlib import Path


def inject_timing_into_core(core_file: str, timing_file: str, output_file: str) -> bool:
    """
    Inject timing constraints into ibex_core.sv

    Args:
        core_file: Path to original ibex_core.sv
        timing_file: Path to timing constraint code
        output_file: Path to write modified ibex_core.sv

    Returns:
        True if successful, False otherwise
    """

    # Read timing constraints
    try:
        with open(timing_file, 'r') as f:
            timing_code = f.read()
    except FileNotFoundError:
        print(f"ERROR: Timing constraint file not found: {timing_file}", file=sys.stderr)
        return False

    # Read core file
    try:
        with open(core_file, 'r') as f:
            core_content = f.read()
    except FileNotFoundError:
        print(f"ERROR: Core file not found: {core_file}", file=sys.stderr)
        return False

    # Find injection point - before ibex_load_store_unit instantiation
    # This is where we have visibility of memory interface signals
    marker = "ibex_load_store_unit"
    injection_point = core_content.find(marker)

    if injection_point == -1:
        print(f"ERROR: Could not find injection point ('{marker}') in {core_file}", file=sys.stderr)
        return False

    # Insert timing constraints before the load_store_unit instantiation
    modified_content = (
        core_content[:injection_point] +
        timing_code + "\n" +
        core_content[injection_point:]
    )

    # Write output
    try:
        with open(output_file, 'w') as f:
            f.write(modified_content)
    except IOError as e:
        print(f"ERROR: Could not write output file {output_file}: {e}", file=sys.stderr)
        return False

    return True


def main():
    parser = argparse.ArgumentParser(
        description='Inject cache timing constraints into ibex_core.sv'
    )
    parser.add_argument('--timing-file', required=True,
                       help='Path to timing constraint code file')
    parser.add_argument('core_file',
                       help='Path to original ibex_core.sv')
    parser.add_argument('output_file',
                       help='Path to write modified ibex_core.sv')
    parser.add_argument('-v', '--verbose', action='store_true',
                       help='Print verbose output')

    args = parser.parse_args()

    if args.verbose:
        print(f"Injecting timing constraints into ibex_core.sv...")
        print(f"  Input core:    {args.core_file}")
        print(f"  Timing file:   {args.timing_file}")
        print(f"  Output core:   {args.output_file}")

    success = inject_timing_into_core(args.core_file, args.timing_file, args.output_file)

    if success:
        if args.verbose:
            print("✓ Successfully injected timing constraints")
        sys.exit(0)
    else:
        print("✗ Failed to inject timing constraints", file=sys.stderr)
        sys.exit(1)


if __name__ == '__main__':
    main()
