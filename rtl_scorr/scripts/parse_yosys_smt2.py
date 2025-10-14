#!/usr/bin/env python3
"""
Parse Yosys SMT2 files to extract structure information.

Extracts module name, state type, signal functions, etc. needed for
generating k-induction queries.
"""

import re

class YosysSMT2Parser:
    """Parser for Yosys-generated SMT2 files."""

    def __init__(self, smt2_file):
        self.smt2_file = smt2_file
        with open(smt2_file, 'r') as f:
            self.content = f.read()

        self.module_name = None
        self.state_type = None
        self.state_constructor = None
        self.signals = {}

        self._parse()

    def _parse(self):
        """Extract structure from SMT2 file."""

        # Extract module name
        match = re.search(r'; yosys-smt2-module (\w+)', self.content)
        if match:
            self.module_name = match.group(1)

        # Extract state type name
        match = re.search(r'\(declare-datatype \|(\w+_s)\|', self.content)
        if match:
            self.state_type = f"|{match.group(1)}|"

        # Extract state constructor
        match = re.search(r'\(\|(\w+_mk)\|', self.content)
        if match:
            self.state_constructor = f"|{match.group(1)}|"

        # Extract signal functions
        # Pattern: (define-fun |module_n signal_name| ((state |module_s|)) Type ...)
        signal_pattern = rf'\(define-fun \|{re.escape(self.module_name)}_n ([^|]+)\|'
        for match in re.finditer(signal_pattern, self.content):
            signal_name = match.group(1)
            self.signals[signal_name] = {
                'func_name': f'|{self.module_name}_n {signal_name}|',
                'name': signal_name,
                'type': 'named'
            }

        # Also extract internal combinational signals (module#N)
        # Pattern: (define-fun |module#N| ((state |module_s|)) Type ...) ; comment
        internal_pattern = rf'\(define-fun \|{re.escape(self.module_name)}#(\d+)\|'
        for match in re.finditer(internal_pattern, self.content):
            signal_id = match.group(1)
            signal_name = f'{self.module_name}#{signal_id}'
            self.signals[signal_name] = {
                'func_name': f'|{signal_name}|',
                'name': signal_name,
                'type': 'internal'
            }

    def get_signal_function(self, signal_name):
        """Get SMT function name for a signal."""
        # Handle both short names and full function names
        # Short: "id_stage_i.mult_en_dec"
        # Full: "|ibex_core_n id_stage_i.mult_en_dec|"

        if signal_name in self.signals:
            return self.signals[signal_name]['func_name']

        # If already a full function name, return as-is
        if signal_name.startswith('|') and signal_name.endswith('|'):
            # Check if this function name exists in our signals
            for sig_info in self.signals.values():
                if sig_info['func_name'] == signal_name:
                    return signal_name
            # Not found in our parsed signals, but might still exist
            # Return it anyway and let caller handle errors
            return signal_name

        return None

    def get_transition_function(self):
        """Get name of transition function."""
        return f"|{self.module_name}_t|"

    def get_assumption_function(self):
        """Get name of assumption function (from assume statements)."""
        return f"|{self.module_name}_u|"

    def get_assertion_function(self):
        """Get name of assertion function."""
        return f"|{self.module_name}_a|"

    def __str__(self):
        return f"""YosysSMT2Parser:
  Module: {self.module_name}
  State type: {self.state_type}
  State constructor: {self.state_constructor}
  Signals: {len(self.signals)}
  Transition function: {self.get_transition_function()}
  Assumption function: {self.get_assumption_function()}
"""

def main():
    import sys
    if len(sys.argv) != 2:
        print("Usage: parse_yosys_smt2.py <smt2_file>")
        sys.exit(1)

    parser = YosysSMT2Parser(sys.argv[1])
    print(parser)

    print("\nAvailable signals:")
    for sig_name in sorted(parser.signals.keys())[:10]:
        print(f"  {sig_name}: {parser.get_signal_function(sig_name)}")

if __name__ == '__main__':
    main()
