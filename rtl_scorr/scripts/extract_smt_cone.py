#!/usr/bin/env python3
"""
Extract cone of influence for specific signals from Yosys SMT2 file.

Given a large SMT2 model and target signals, extract only the logic cone
needed to reason about those signals. This dramatically reduces model size
for targeted equivalence checking.

Strategy:
1. Parse SMT2 to build dependency graph
2. Starting from target signals, walk backwards to find all dependencies
3. Generate new SMT2 with only the required definitions
4. Include state type, transition, and assumption functions
"""

import sys
import re
from pathlib import Path
from typing import Set, Dict, List, Tuple


class SMT2ConeExtractor:
    """Extract logic cone from Yosys SMT2 files."""

    def __init__(self, smt2_file):
        self.smt2_file = Path(smt2_file)
        with open(smt2_file, 'r') as f:
            self.content = f.read()
            self.lines = self.content.split('\n')

        # Extracted components
        self.module_name = None
        self.state_type = None
        self.state_def = []  # Lines defining the state datatype
        self.signals = {}    # signal_name -> definition lines
        self.dependencies = {}  # signal_name -> set of signals it depends on

        # Special functions
        self.transition_func = []
        self.assumption_func = []
        self.assertion_func = []

        self._parse()

    def _parse(self):
        """Parse SMT2 file to extract structure and dependencies."""

        # Extract module name
        match = re.search(r'; yosys-smt2-module (\S+)', self.content)
        if match:
            self.module_name = match.group(1)

        # Extract state datatype definition
        in_state_def = False
        paren_depth = 0
        state_start_line = None

        for i, line in enumerate(self.lines):
            if 'declare-datatype' in line and '_s|' in line:
                in_state_def = True
                state_start_line = i
                # Extract state type name
                match = re.search(r'\|([^|]+_s)\|', line)
                if match:
                    self.state_type = f"|{match.group(1)}|"

            if in_state_def:
                paren_depth += line.count('(') - line.count(')')
                if paren_depth == 0:
                    self.state_def = self.lines[state_start_line:i+1]
                    in_state_def = False

        # Extract signal definitions and build dependency graph
        self._extract_signals()

        # Extract special functions (transition, assumption, assertion)
        self._extract_special_functions()

    def _extract_signals(self):
        """Extract all signal definitions and their dependencies."""

        current_signal = None
        signal_start = None
        paren_depth = 0

        for i, line in enumerate(self.lines):
            # Look for define-fun that's a signal (takes state as parameter)
            if 'define-fun' in line and f'((state {self.state_type}))' in line:
                # Extract signal name
                match = re.search(r'define-fun (\|[^|]+\|)', line)
                if match:
                    current_signal = match.group(1)
                    signal_start = i
                    paren_depth = line.count('(') - line.count(')')
                    continue

            if current_signal:
                paren_depth += line.count('(') - line.count(')')
                if paren_depth == 0:
                    # End of signal definition
                    signal_lines = self.lines[signal_start:i+1]
                    self.signals[current_signal] = signal_lines

                    # Extract dependencies
                    deps = self._extract_dependencies('\n'.join(signal_lines))
                    self.dependencies[current_signal] = deps

                    current_signal = None

    def _extract_dependencies(self, signal_def: str) -> Set[str]:
        """Extract which signals this definition depends on."""
        deps = set()

        # Look for calls to other signal functions
        # Pattern: (|signal_name| state) or (|module#N| state)
        pattern = r'\((\|[^|]+\|)\s+state\)'
        for match in re.finditer(pattern, signal_def):
            dep_signal = match.group(1)
            deps.add(dep_signal)

        # Also look for state field accesses directly
        # Pattern: (|module#N| state) which accesses state field
        # These are already handled above

        # Look for direct state field references (module#N without function call)
        # These appear in the state datatype constructor
        pattern = r'\|([^|]+#\d+)\|'
        for match in re.finditer(pattern, signal_def):
            state_field = f"|{match.group(1)}|"
            # Check if this corresponds to a signal function
            for sig_name in self.signals.keys():
                if state_field in sig_name or state_field == sig_name:
                    deps.add(sig_name)
                    break

        return deps

    def _extract_special_functions(self):
        """Extract transition, assumption, and assertion functions."""

        # Transition function: |module_t|
        # Assumption function: |module_u|
        # Assertion function: |module_a|

        suffixes = {
            '_t|': 'transition',
            '_u|': 'assumption',
            '_a|': 'assertion'
        }

        for suffix, func_type in suffixes.items():
            pattern = rf'define-fun (\|[^|]+{re.escape(suffix)})'

            current_func = None
            func_start = None
            paren_depth = 0

            for i, line in enumerate(self.lines):
                if current_func is None and re.search(pattern, line):
                    current_func = func_type
                    func_start = i
                    paren_depth = line.count('(') - line.count(')')
                    continue

                if current_func:
                    paren_depth += line.count('(') - line.count(')')
                    if paren_depth == 0:
                        func_lines = self.lines[func_start:i+1]

                        if func_type == 'transition':
                            self.transition_func = func_lines
                        elif func_type == 'assumption':
                            self.assumption_func = func_lines
                        elif func_type == 'assertion':
                            self.assertion_func = func_lines

                        current_func = None

    def compute_cone(self, target_signals: List[str]) -> Set[str]:
        """
        Compute logic cone for target signals.

        Returns set of all signals (including state fields) needed to compute targets.
        """
        cone = set()
        worklist = list(target_signals)

        while worklist:
            signal = worklist.pop()
            if signal in cone:
                continue

            cone.add(signal)

            # Add dependencies to worklist
            if signal in self.dependencies:
                for dep in self.dependencies[signal]:
                    if dep not in cone:
                        worklist.append(dep)

        return cone

    def extract_cone_smt2(self, target_signals: List[str]) -> str:
        """
        Generate minimal SMT2 model containing only the logic cone for targets.
        """

        # Compute cone
        cone = self.compute_cone(target_signals)

        # Build minimal SMT2
        output = []

        # Header comment
        output.append("; SMT2 Cone Extraction")
        output.append(f"; Original file: {self.smt2_file.name}")
        output.append(f"; Target signals: {', '.join(target_signals)}")
        output.append(f"; Cone size: {len(cone)} signals (from {len(self.signals)} total)")
        output.append("")

        # Copy preamble (comments, set-logic, etc.)
        for line in self.lines[:10]:
            if line.startswith(';') or line.startswith('(set-'):
                output.append(line)
        output.append("")

        # State datatype definition
        output.extend(self.state_def)
        output.append("")

        # Include only signals in cone
        output.append(f"; Signal definitions ({len(cone)} in cone)")
        for signal in sorted(cone):
            if signal in self.signals:
                output.extend(self.signals[signal])
        output.append("")

        # Special functions
        if self.transition_func:
            output.append("; Transition function")
            output.extend(self.transition_func)
            output.append("")

        if self.assumption_func:
            output.append("; Assumption function")
            output.extend(self.assumption_func)
            output.append("")

        if self.assertion_func:
            output.append("; Assertion function")
            output.extend(self.assertion_func)
            output.append("")

        return '\n'.join(output)

    def extract_and_save(self, target_signals: List[str], output_file: Path):
        """Extract cone and save to file."""
        cone_smt2 = self.extract_cone_smt2(target_signals)

        with open(output_file, 'w') as f:
            f.write(cone_smt2)

        # Compute statistics
        original_lines = len(self.lines)
        cone_lines = len(cone_smt2.split('\n'))
        reduction = 100 * (1 - cone_lines / original_lines)

        print(f"✓ Extracted cone to: {output_file}")
        print(f"  Original: {original_lines} lines, {len(self.signals)} signals")
        print(f"  Cone:     {cone_lines} lines ({reduction:.1f}% reduction)")

        return cone_lines, original_lines


def main():
    if len(sys.argv) < 4:
        print("Usage: extract_smt_cone.py <smt2_file> <output_file> <signal1> [signal2 ...]")
        print("")
        print("Example:")
        print("  extract_smt_cone.py input.smt2 output.smt2 'mult_en_dec' 'div_en_dec'")
        print("")
        print("Extracts logic cone for specified signals, reducing SMT model size.")
        sys.exit(1)

    smt2_file = sys.argv[1]
    output_file = sys.argv[2]
    target_signals = sys.argv[3:]

    if not Path(smt2_file).exists():
        print(f"ERROR: File not found: {smt2_file}")
        sys.exit(1)

    print("=" * 80)
    print("SMT2 CONE EXTRACTION")
    print("=" * 80)
    print()

    # Parse and extract
    extractor = SMT2ConeExtractor(smt2_file)

    # Format target signals (add | delimiters if needed)
    formatted_targets = []
    for sig in target_signals:
        if not sig.startswith('|'):
            # Try to find matching signal
            found = False
            for known_sig in extractor.signals.keys():
                if sig in known_sig:
                    formatted_targets.append(known_sig)
                    found = True
                    break
            if not found:
                print(f"WARNING: Signal '{sig}' not found in SMT2 file")
                formatted_targets.append(f"|{sig}|")
        else:
            formatted_targets.append(sig)

    # Extract cone
    extractor.extract_and_save(formatted_targets, Path(output_file))


if __name__ == '__main__':
    main()
