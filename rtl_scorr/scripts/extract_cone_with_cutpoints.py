#!/usr/bin/env python3
"""
Extract SMT2 cone with cut-points for assumed inputs.

Strategy:
1. Identify cut-points (inputs with assumptions): instr_rdata_i, rst_ni, etc.
2. Extract cone from target signal, stopping at cut-points
3. Replace cut-point computations with declare-const (free variables)
4. Add DSL constraints on those free variables
5. Result: Minimal cone with proper assumptions!
"""

import sys
import re
from pathlib import Path
from typing import Set, List
from smt_cone_extractor_v2 import SimpleSMT2ConeExtractor


def extract_cone_with_cutpoints(
    smt2_file: Path,
    target_signal: str,
    cutpoint_signals: List[str],
    dsl_constraints: str,
    output_file: Path
) -> bool:
    """
    Extract cone with cut-points.

    Args:
        smt2_file: Full SMT2 model
        target_signal: Signal to check (e.g., mult_en_dec)
        cutpoint_signals: Signals to treat as free variables (e.g., instr_rdata_i)
        dsl_constraints: SMT2 constraints to assert on cut-points
        output_file: Output SMT2 file
    """

    extractor = SimpleSMT2ConeExtractor(smt2_file)

    # Convert cutpoint names to SMT2 function names
    cutpoint_funcs = set()
    for sig in cutpoint_signals:
        # Find matching functions
        for func_name in extractor.definitions.keys():
            if sig in func_name:
                cutpoint_funcs.add(func_name)

    print(f"Cut-points: {len(cutpoint_funcs)} functions")
    for cp in sorted(cutpoint_funcs)[:5]:
        print(f"  {cp}")

    # Extract cone, stopping at cut-points
    cone = set()
    worklist = [target_signal]

    while worklist:
        func = worklist.pop()

        if func not in extractor.definitions:
            continue

        if func in cone:
            continue

        # If we hit a cut-point, include it but don't expand its dependencies
        if func in cutpoint_funcs:
            cone.add(func)  # Include the cut-point function itself
            continue  # But don't expand its dependencies

        cone.add(func)

        # Add dependencies
        deps = extractor.find_references(extractor.definitions[func])
        for dep in deps:
            if dep not in cone:
                worklist.append(dep)

    print(f"Cone (stopping at cut-points): {len(cone)} functions")

    # Build SMT2
    lines = []
    lines.append("; Minimal cone with cut-point assumptions")
    lines.append(f"; Target: {target_signal}")
    lines.append(f"; Cone: {len(cone)} functions")
    lines.append(f"; Cut-points: {len(cutpoint_funcs)}")
    lines.append("")

    # Use ALL logic (most permissive - supports everything)
    lines.append("(set-logic ALL)")
    lines.append("")

    # Datatype (includes cut-points as fields, but we'll override them)
    lines.append(extractor.datatype)
    lines.append("")

    # DSL constraints on cut-points
    lines.append("; DSL constraints on cut-point inputs")
    lines.append(dsl_constraints)
    lines.append("")

    # Cone functions
    lines.append(f"; Cone functions ({len(cone)})")
    for line_content in extractor.content.split('\n'):
        if '(define-fun' in line_content:
            match = re.search(r'define-fun (\|[^|]+\|)', line_content)
            if match and match.group(1) in cone:
                lines.append(extractor.definitions[match.group(1)])

    # Transition function (needed for k-induction)
    trans_func = f"|{extractor.module_name}_t|"
    if trans_func in extractor.definitions:
        lines.append("")
        lines.append("; Transition function")
        lines.append(extractor.definitions[trans_func])

    # Stub assumption function (since we're using DSL constraints directly)
    state_type_match = re.search(r'\|([^|]+_s)\|', extractor.datatype)
    state_type = f"|{state_type_match.group(1)}|" if state_type_match else "|state_s|"
    lines.append("")
    lines.append("; Assumption function (stubbed - using DSL constraints instead)")
    lines.append(f"(define-fun |{extractor.module_name}_u| ((state {state_type})) Bool true)")

    output_file.write_text('\n'.join(lines))

    return True


def main():
    if len(sys.argv) < 4:
        print("Usage: extract_cone_with_cutpoints.py <smt2> <dsl_constraints.smt2> <target> <output>")
        print("")
        print("Example:")
        print("  extract_cone_with_cutpoints.py ibex.smt2 constraints.smt2 '|..mult_en_dec|' cone.smt2")
        sys.exit(1)

    smt2_file = Path(sys.argv[1])
    dsl_constraints_file = Path(sys.argv[2])
    target = sys.argv[3]
    output = Path(sys.argv[4])

    dsl_constraints = dsl_constraints_file.read_text()

    # Default cut-points for Ibex
    cutpoints = ['instr_rdata_i', 'rst_ni', 'instr_is_compressed']

    print("=" * 80)
    print("CONE EXTRACTION WITH CUT-POINTS")
    print("=" * 80)
    print(f"Target: {target}")
    print(f"Cut-points: {', '.join(cutpoints)}")
    print()

    extract_cone_with_cutpoints(smt2_file, target, cutpoints, dsl_constraints, output)

    lines = len(output.read_text().split('\n'))
    print(f"\n✓ Generated: {output} ({lines} lines)")


if __name__ == '__main__':
    main()
