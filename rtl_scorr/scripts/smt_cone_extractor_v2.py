#!/usr/bin/env python3
"""
Simplified SMT2 cone extractor that uses text-based dependency tracking.

Strategy:
1. Parse SMT2 to find all (define-fun ...) definitions
2. For each target signal, recursively find all references in its body
3. Include all referenced definitions in output
"""

import sys
import re
from pathlib import Path
from typing import Set, Dict, List


class SimpleSMT2ConeExtractor:
    """Simple text-based cone extractor for SMT2 files."""

    def __init__(self, smt2_file):
        self.smt2_file = Path(smt2_file)
        self.content = self.smt2_file.read_text()

        # Parse into sections
        self.header = []  # Comments, set-logic, etc.
        self.datatype = ""  # State datatype definition
        self.definitions = {}  # name -> full definition text
        self.module_name = ""

        self._parse()

    def _parse(self):
        """Parse SMT2 into sections."""
        lines = self.content.split('\n')

        # Extract module name
        for line in lines:
            if 'yosys-smt2-module' in line:
                match = re.search(r'yosys-smt2-module (\S+)', line)
                if match:
                    self.module_name = match.group(1)

        # Parse definitions
        i = 0
        while i < len(lines):
            line = lines[i]

            # Datatype/sort definition (check this BEFORE header to avoid catching it in header)
            if 'declare-datatype' in line or 'declare-sort' in line or 'define-sort' in line:
                # For define-sort (used with -stbv), it's usually just one line
                if 'define-sort' in line and line.count('(') == line.count(')'):
                    self.datatype = line
                    i += 1
                    continue

                # For declare-datatype/declare-sort, find matching closing paren
                start = i
                depth = line.count('(') - line.count(')')  # Start with count from first line
                i += 1
                while i < len(lines) and depth > 0:
                    depth += lines[i].count('(') - lines[i].count(')')
                    i += 1
                self.datatype = '\n'.join(lines[start:i])
                continue

            # Header (comments, preamble)
            if line.startswith(';') or line.startswith('(set-'):
                self.header.append(line)
                i += 1
                continue

            # Function definition
            if line.strip().startswith('(define-fun'):
                # Extract function name
                match = re.search(r'define-fun (\|[^|]+\|)', line)
                if match:
                    func_name = match.group(1)

                    # Find matching closing paren
                    start = i
                    depth = line.count('(') - line.count(')')  # Start with count from first line
                    i += 1
                    while i < len(lines) and depth > 0:
                        depth += lines[i].count('(') - lines[i].count(')')
                        i += 1

                    func_def = '\n'.join(lines[start:i])
                    self.definitions[func_name] = func_def
                    continue

            i += 1

    def find_references(self, text: str) -> Set[str]:
        """
        Find all function references in text.

        Handles both:
        - Function calls: (|func_name| state)
        - State field accessors: (|module#N| state)
        """
        refs = set()

        # Find all function call patterns: (|name| ...)
        # This captures both regular function calls and state field accessors
        pattern = r'\(\|([^|]+)\|'
        for match in re.finditer(pattern, text):
            name = f"|{match.group(1)}|"
            if name in self.definitions:
                refs.add(name)

        return refs

    def compute_cone(self, targets: List[str]) -> Set[str]:
        """Compute transitive closure of dependencies for targets."""
        cone = set()
        worklist = list(targets)

        while worklist:
            func = worklist.pop()

            if func not in self.definitions:
                continue

            if func in cone:
                continue

            cone.add(func)

            # Find references in this function's definition
            refs = self.find_references(self.definitions[func])

            for ref in refs:
                if ref not in cone:
                    worklist.append(ref)

        return cone

    def extract_cone(self, targets: List[str], stub_assumptions: bool = False) -> str:
        """
        Extract minimal SMT2 model for targets.

        Args:
            targets: List of target signal names
            stub_assumptions: If True, replace assumption functions with stubs
                            (declare as uninterpreted, always return true)
        """

        # Compute cone for the target signals ONLY
        cone = self.compute_cone(targets)

        # Find special functions
        special_funcs = []
        assumption_funcs = []
        other_special = []

        for func_name in self.definitions.keys():
            if '_u|' in func_name or '_u ' in func_name:
                # Assumption functions - handle specially if stubbing
                assumption_funcs.append(func_name)
                if not stub_assumptions:
                    cone.add(func_name)
            elif any(pattern in func_name for pattern in ['_t|', '_a|', '_i|', '_h|']):
                # Transition, assertion, init, hierarchy - always include
                other_special.append(func_name)
                cone.add(func_name)

        special_funcs = assumption_funcs + other_special

        # Build output
        lines = []

        # Header
        lines.append("; SMT2 Cone Extraction")
        lines.append(f"; Source: {self.smt2_file.name}")
        lines.append(f"; Module: {self.module_name}")
        lines.append(f"; Targets: {', '.join(targets)}")
        lines.append(f"; Cone: {len(cone)} functions (from {len(self.definitions)} total)")
        lines.append(f"; Special functions: {len(special_funcs)}")
        lines.append("")

        # Preamble
        lines.extend(self.header[:8])  # First few header lines
        lines.append("")

        # Datatype
        lines.append(self.datatype)
        lines.append("")

        # Functions in cone
        # Output in original file order (which should already be topologically sorted)
        lines.append(f"; Function definitions ({len(cone)} in cone)")

        # Get functions from original file in their original order
        original_order = []
        for line_content in self.content.split('\n'):
            if '(define-fun' in line_content:
                match = re.search(r'define-fun (\|[^|]+\|)', line_content)
                if match and match.group(1) in cone:
                    original_order.append(match.group(1))

        # Output in original order (Yosys already sorted them topologically)
        for func_name in original_order:
            if func_name in cone:
                lines.append(self.definitions[func_name])

        # Always include special functions at the end
        lines.append("")

        if stub_assumptions and assumption_funcs:
            # Stub out assumption functions (declare as returning true)
            lines.append(f"; Assumption functions (stubbed - {len(assumption_funcs)} total)")
            lines.append("; These are axioms, so we declare them to always return true")
            for func_name in sorted(assumption_funcs):
                # Create stub that always returns true
                lines.append(f"(define-fun {func_name} ((state {self.state_type})) Bool true)")

        # Include other special functions (transition, etc.) normally
        if other_special:
            lines.append("")
            lines.append(f"; Other special functions ({len(other_special)} total)")
            for func_name in sorted(other_special):
                if func_name in self.definitions:
                    lines.append(self.definitions[func_name])

        # If not stubbing, include all special functions normally
        if not stub_assumptions:
            for func_name in sorted(special_funcs):
                if func_name not in cone and func_name in self.definitions:
                    lines.append(self.definitions[func_name])

        return '\n'.join(lines)


def main():
    if len(sys.argv) < 4:
        print("Usage: smt_cone_extractor_v2.py <smt2_file> <output_file> <target1> [target2 ...]")
        print("")
        print("Example:")
        print("  smt_cone_extractor_v2.py input.smt2 output.smt2 '|signal_a|' '|signal_b|'")
        sys.exit(1)

    smt2_file = Path(sys.argv[1])
    output_file = Path(sys.argv[2])
    targets = sys.argv[3:]

    if not smt2_file.exists():
        print(f"ERROR: File not found: {smt2_file}")
        sys.exit(1)

    print("=" * 80)
    print("SMT2 CONE EXTRACTION (Simplified)")
    print("=" * 80)

    # Extract
    extractor = SimpleSMT2ConeExtractor(smt2_file)

    # Normalize target names (add | if needed)
    normalized_targets = []
    for t in targets:
        if not t.startswith('|'):
            t = f"|{t}|"
        normalized_targets.append(t)

    cone_smt2 = extractor.extract_cone(normalized_targets)

    # Save
    output_file.write_text(cone_smt2)

    # Stats
    original_lines = len(extractor.content.split('\n'))
    cone_lines = len(cone_smt2.split('\n'))
    reduction = 100 * (1 - cone_lines / original_lines)

    print(f"✓ Extracted to: {output_file}")
    print(f"  Original: {original_lines} lines, {len(extractor.definitions)} functions")
    print(f"  Cone:     {cone_lines} lines, {len(extractor.compute_cone(normalized_targets))} functions")
    print(f"  Reduction: {reduction:.1f}%")


if __name__ == '__main__':
    main()
