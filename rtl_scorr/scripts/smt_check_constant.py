#!/usr/bin/env python3
"""
Check if an RTL signal is provably constant using SMT k-induction.

This is essential for finding dead code - signals that are constant
under the given constraints (assumptions from outlawed instructions).
"""

import sys
import subprocess
import tempfile
from pathlib import Path
from parse_yosys_smt2 import YosysSMT2Parser


def create_constant_check_query(parser, signal, constant_value, k=2):
    """
    Create SMT2 k-induction query to check if signal is constant.

    Strategy:
    - Apply assumptions at all time steps
    - Apply state transitions
    - Try to make signal differ from constant value
    - If UNSAT → signal is provably constant!

    Args:
        parser: YosysSMT2Parser with loaded model
        signal: Signal name (e.g., '|ibex_core_n id_stage_i.mult_en_dec|')
        constant_value: Expected constant (0 or 1 for Bool, bit-vector for larger)
        k: K-induction depth

    Returns:
        (query_string, error_message)
    """

    sig_func = parser.get_signal_function(signal)
    if not sig_func:
        return None, f"Signal not found: {signal}"

    # Read base SMT2 model
    with open(parser.smt2_file, 'r') as f:
        smt2_base = f.read()

    # Find the signal definition to determine type
    sig_def = None
    for line in smt2_base.split('\n'):
        if f'define-fun {sig_func}' in line:
            sig_def = line
            break

    if not sig_def:
        return None, f"Signal definition not found for {signal}"

    # Determine type from definition
    is_bool = 'Bool' in sig_def and 'BitVec' not in sig_def

    if is_bool:
        # Boolean signal
        if constant_value == 0:
            const_expr = "false"
        elif constant_value == 1:
            const_expr = "true"
        else:
            return None, f"Invalid constant for Bool: {constant_value}"
    else:
        # Bit-vector signal - assume width 1 for Bool-like signals
        const_expr = f"#b{constant_value}"

    # SIMPLE APPROACH: Just append our check to the existing SMT2 model
    # The model already has all declarations, functions, etc.
    query = smt2_base + f"""

; ============================================================================
; K-Induction Constant Check (appended)
; ============================================================================
; Checking: {signal} ≡ constant {constant_value}
; K-depth: {k}

; Declare states for k+1 time steps
"""

    # Declare state variables
    for t in range(k + 1):
        query += f"(declare-const s{t} {parser.state_type})\n"

    query += "\n; Apply design assumptions (from assume statements) at all time steps\n"
    for t in range(k + 1):
        query += f"(assert ({parser.get_assumption_function()} s{t}))\n"

    # Apply transitions
    query += "\n; Apply state transitions\n"
    for t in range(k):
        query += f"(assert ({parser.get_transition_function()} s{t} s{t+1}))\n"

    # For constant checking, we use a simplified approach:
    # Just try to make the signal non-constant at ANY time step
    query += f"\n; Try to make signal differ from constant {constant_value}\n"
    query += "; If UNSAT → signal is provably constant!\n"

    if is_bool:
        # For boolean signals
        query += f"(assert (or"
        for t in range(k + 1):
            query += f"\n  (not (= ({sig_func} s{t}) {const_expr}))"
        query += "\n))\n"
    else:
        # For bit-vector signals
        query += f"(assert (or"
        for t in range(k + 1):
            query += f"\n  (not (= ({sig_func} s{t}) {const_expr}))"
        query += "\n))\n"

    query += "\n; Check satisfiability\n"
    query += "; If UNSAT → signal is provably constant!\n"
    query += "; If SAT → signal can differ from constant\n"
    query += "(check-sat)\n"

    return query, None


def check_constant_with_z3(query, timeout=30, save_query_to=None):
    """Run Z3 on SMT query to check if signal is constant."""

    # Write query to temp file
    if save_query_to:
        query_file = save_query_to
        with open(query_file, 'w') as f:
            f.write(query)
        delete_after = False
    else:
        with tempfile.NamedTemporaryFile(mode='w', suffix='.smt2', delete=False) as f:
            f.write(query)
            query_file = f.name
        delete_after = True

    try:
        result = subprocess.run(
            ['z3', '-smt2', query_file],
            capture_output=True,
            text=True,
            timeout=timeout
        )

        if delete_after:
            Path(query_file).unlink()

        # Parse result
        stdout_lower = result.stdout.lower()
        if 'unsat' in stdout_lower:
            return 'CONSTANT'  # Signal is provably constant
        elif 'sat' in stdout_lower and 'unsat' not in stdout_lower:
            return 'NOT_CONSTANT'  # Signal can vary
        else:
            return f'UNKNOWN ({result.stdout.strip()[:50]})'

    except subprocess.TimeoutExpired:
        if delete_after:
            Path(query_file).unlink()
        return 'TIMEOUT'
    except FileNotFoundError:
        if delete_after and Path(query_file).exists():
            Path(query_file).unlink()
        return 'Z3_NOT_FOUND'


def main():
    if len(sys.argv) < 4:
        print("Usage: smt_check_constant.py <smt2_file> <signal> <constant_value> [k]")
        print("")
        print("Example:")
        print("  smt_check_constant.py model.smt2 '|ibex_core_n mult_en_dec|' 0 2")
        print("")
        print("Checks if signal is provably constant using SMT k-induction")
        sys.exit(1)

    smt2_file = Path(sys.argv[1])
    signal = sys.argv[2]
    constant_value = int(sys.argv[3])
    k = int(sys.argv[4]) if len(sys.argv) > 4 else 2

    if not smt2_file.exists():
        print(f"ERROR: SMT2 file not found: {smt2_file}")
        sys.exit(1)

    print("=" * 80)
    print("SMT K-INDUCTION CONSTANT CHECK")
    print("=" * 80)
    print(f"Signal:   {signal}")
    print(f"Constant: {constant_value}")
    print(f"K-depth:  {k}")
    print()

    # Parse SMT2 structure
    print("Parsing SMT2 file...")
    parser = YosysSMT2Parser(smt2_file)
    print(f"  Module: {parser.module_name}")
    print(f"  Signals: {len(parser.signals)}")
    print()

    # Create constant check query
    print("Generating k-induction query...")
    query, error = create_constant_check_query(parser, signal, constant_value, k)

    if error:
        print(f"ERROR: {error}")
        sys.exit(1)

    # Save query for debugging
    query_file = smt2_file.parent / f"check_{signal.replace('|', '').replace(' ', '_').replace('.', '_')}_const.smt2"
    print(f"  Saved query to: {query_file}")

    # Check with Z3 (use longer timeout from command line if provided)
    timeout_val = int(sys.argv[5]) if len(sys.argv) > 5 else 120
    print(f"\nRunning Z3 (timeout: {timeout_val}s)...")
    result = check_constant_with_z3(query, timeout=timeout_val, save_query_to=query_file)

    print()
    print("=" * 80)
    if result == 'CONSTANT':
        print(f"✓ PROVEN CONSTANT: {signal} ≡ {constant_value}")
    elif result == 'NOT_CONSTANT':
        print(f"✗ NOT CONSTANT: {signal} can vary")
    elif result == 'TIMEOUT':
        print(f"⏱ TIMEOUT: Could not prove within 30 seconds")
    elif result == 'Z3_NOT_FOUND':
        print(f"✗ ERROR: Z3 not found (install with: sudo apt install z3)")
    else:
        print(f"? UNKNOWN: {result}")
    print("=" * 80)

    sys.exit(0 if result == 'CONSTANT' else 1)


if __name__ == '__main__':
    main()
