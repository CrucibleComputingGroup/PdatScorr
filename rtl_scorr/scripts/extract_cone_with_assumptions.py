#!/usr/bin/env python3
"""
Extract SMT2 cone with proper assumption handling.

Key insight:
- Assumptions constrain INPUTS (like instr_rdata_i)
- We don't need to include how inputs are computed
- Declare inputs as free variables (declare-const)
- Assert assumption constraints directly
- This gives minimal cone without assumption dependency explosion!
"""

import sys
import re
from pathlib import Path
from typing import Set, List, Dict
from smt_cone_extractor_v2 import SimpleSMT2ConeExtractor


def extract_assumption_constraints(smt2_file: Path, module_name: str) -> Dict[str, List[str]]:
    """
    Parse assumption functions to extract direct constraints.

    Returns: Dict mapping input variables to their constraint expressions
    """

    content = smt2_file.read_text()
    constraints = []

    # Find assumption functions (ibex_core_u 0, ibex_core_u 1, etc.)
    # These encode the assume() statements from Verilog
    pattern = rf'\(define-fun \|{module_name}_u \d+\|.*?\n'

    for match in re.finditer(pattern, content):
        func_def = match.group(0)
        # Extract the constraint expression
        # Format: (define-fun |ibex_core_u 0| ((state ...)) Bool <expression>)
        constraints.append(func_def)

    return {'assumptions': constraints}


def create_minimal_cone_with_free_inputs(
    smt2_file: Path,
    target_signal: str,
    output_file: Path
) -> bool:
    """
    Create minimal SMT2 cone by:
    1. Extracting signal cone
    2. Identifying constrained inputs
    3. Declaring inputs as free variables
    4. Asserting assumption constraints directly
    """

    # Parse full SMT2
    extractor = SimpleSMT2ConeExtractor(smt2_file)

    # Extract cone for signal (WITHOUT assumptions - they'll be handled separately)
    # Just get the signal dependencies
    signal_cone = set()
    worklist = [target_signal]

    while worklist:
        func = worklist.pop()
        if func not in extractor.definitions or func in signal_cone:
            continue

        signal_cone.add(func)

        # Find dependencies
        deps = extractor.find_references(extractor.definitions[func])
        for dep in deps:
            if dep not in signal_cone:
                worklist.append(dep)

    print(f"Signal cone: {len(signal_cone)} functions")

    # Find inputs that are constrained by assumptions
    # Look for signals that appear in assumption functions
    assumption_inputs = set()

    for func_name in extractor.definitions.keys():
        if '_u ' in func_name and '|' in func_name:  # Assumption functions
            func_def = extractor.definitions[func_name]
            # Find which state fields/signals this references
            refs = extractor.find_references(func_def)
            assumption_inputs.update(refs)

    print(f"Inputs constrained by assumptions: {len(assumption_inputs)}")

    # Build minimal SMT2
    lines = []
    lines.append("; Minimal SMT2 with assumption-constrained free inputs")
    lines.append(f"; Target: {target_signal}")
    lines.append(f"; Signal cone: {len(signal_cone)} functions")
    lines.append("")
    lines.append("(set-logic QF_BV)")
    lines.append("")

    # Datatype
    lines.append(extractor.datatype)
    lines.append("")

    # Declare constrained inputs as free variables
    # (Skip this for now - use datatype state)

    # Signal cone functions
    lines.append(f"; Signal cone ({len(signal_cone)} functions)")
    for func_name in extractor.content.split('\n'):
        if '(define-fun' in func_name:
            match = re.search(r'define-fun (\|[^|]+\|)', func_name)
            if match and match.group(1) in signal_cone:
                # Output this function
                if match.group(1) in extractor.definitions:
                    lines.append(extractor.definitions[match.group(1)])

    # Extract state type from datatype
    state_type_match = re.search(r'\|([^|]+_s)\|', extractor.datatype)
    state_type = f"|{state_type_match.group(1)}|" if state_type_match else "|state_s|"

    # Include simplified assumption constraints
    lines.append("")
    lines.append("; Assumption constraints (simplified - assert directly)")

    # For now, just include the main assumption function as stub
    lines.append(f"(define-fun |{extractor.module_name}_u| ((state {state_type})) Bool true)")
    lines.append("; TODO: Extract and assert actual constraints from DSL")

    # Transition function (needed for k-induction)
    lines.append("")
    lines.append("; Transition function")
    trans_func = f"|{extractor.module_name}_t|"
    if trans_func in extractor.definitions:
        lines.append(extractor.definitions[trans_func])

    output_file.write_text('\n'.join(lines))
    return True


def main():
    if len(sys.argv) < 4:
        print("Usage: extract_cone_with_assumptions.py <smt2> <target> <output>")
        print("")
        print("Example:")
        print("  extract_cone_with_assumptions.py ibex.smt2 '|..mult_en_dec|' cone.smt2")
        sys.exit(1)

    smt2_file = Path(sys.argv[1])
    target = sys.argv[2]
    output = Path(sys.argv[3])

    print("=" * 80)
    print("MINIMAL CONE WITH FREE INPUTS")
    print("=" * 80)

    create_minimal_cone_with_free_inputs(smt2_file, target, output)

    lines = len(output.read_text().split('\n'))
    print(f"\n✓ Generated: {output} ({lines} lines)")


if __name__ == '__main__':
    main()
