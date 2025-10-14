#!/usr/bin/env python3
"""
SMT-based RTL signal constancy checker.

Uses Yosys to generate SMT2 model, then queries Z3 to check if specific
RTL signals are provably constant under the given constraints.
"""

import sys
import subprocess
import tempfile
import re
from pathlib import Path

def generate_smt_model(id_stage_path, output_smt2):
    """Generate SMT2 model from RTL using Yosys."""

    import os
    cwd = os.getcwd()

    yosys_script = f"""# Generate SMT2 model for RTL signal analysis
# Preserve hierarchy and signal names

read_systemverilog \\
  -I{cwd}/cores/ibex/rtl \\
  -I{cwd}/cores/ibex/shared/rtl \\
  -I{cwd}/cores/ibex/vendor/lowrisc_ip/ip/prim/rtl \\
  -I{cwd}/cores/ibex/vendor/lowrisc_ip/dv/sv/dv_utils \\
  -DYOSYS=1 -DSYNTHESIS=1 \\
  ./cores/ibex/rtl/ibex_pkg.sv \\
  ./cores/ibex/rtl/ibex_decoder.sv \\
  ./cores/ibex/rtl/ibex_alu.sv \\
  ./cores/ibex/rtl/ibex_compressed_decoder.sv \\
  ./cores/ibex/rtl/ibex_controller.sv \\
  {id_stage_path} \\
  ./cores/ibex/rtl/ibex_ex_block.sv \\
  ./cores/ibex/rtl/ibex_multdiv_fast.sv \\
  ./cores/ibex/rtl/ibex_multdiv_slow.sv

# Set top to ID stage to keep it manageable
hierarchy -check -top ibex_id_stage

# Process but don't flatten - preserve structure
proc
opt

# Prepare for SMT2 export (simplify flip-flops)
async2sync
dffunmap

# Generate SMT2 model
# -wires: include all wire declarations
# -stbv: use state bits as bit-vectors (better for SMT)
write_smt2 -wires -stbv -stdt {output_smt2}
"""

    with tempfile.NamedTemporaryFile(mode='w', suffix='.ys', delete=False) as f:
        f.write(yosys_script)
        script_path = f.name

    print(f"Generating SMT2 model...")
    # Use synlig for SystemVerilog support
    result = subprocess.run(
        ['synlig', '-s', script_path],
        capture_output=True,
        text=True
    )

    # Clean up script
    Path(script_path).unlink()

    if result.returncode != 0:
        print("ERROR: Yosys SMT generation failed")
        print(result.stderr)
        return False

    print(f"✓ Generated SMT2 model: {output_smt2}")
    return True

def create_signal_constancy_query(smt2_base, signal_name, expected_value):
    """
    Create SMT2 query to check if signal is constant.

    Returns query that is:
    - UNSAT if signal is provably constant
    - SAT if signal can vary
    """

    query = f"""; Check if {signal_name} is constant {expected_value}
; Generated query for RTL signal constancy checking

(include "{smt2_base}")

; Try to find a case where signal != expected value
; If UNSAT, signal is provably constant!
(assert (not (= {signal_name} {expected_value})))

(check-sat)
(get-model)
"""
    return query

def check_signal_with_z3(smt2_file, signal_checks):
    """
    Check multiple signals using Z3.

    signal_checks: list of (signal_name, expected_value, description)
    """

    if not Path(smt2_file).exists():
        print(f"ERROR: SMT2 file not found: {smt2_file}")
        return []

    # First, extract available signals from SMT2 file
    with open(smt2_file, 'r') as f:
        smt_content = f.read()

    # Find all declared signals
    declared_signals = re.findall(r'\(define-fun (\w+) \(\)', smt_content)

    print(f"\nFound {len(declared_signals)} signals in SMT2 model")
    print(f"Checking {len(signal_checks)} signals for constancy...")
    print()

    results = []

    for signal_name, expected_value, description in signal_checks:
        # Check if signal exists in model
        if signal_name not in smt_content:
            results.append({
                'signal': signal_name,
                'description': description,
                'status': 'NOT_FOUND',
                'message': 'Signal not found in SMT2 model (may be optimized away or renamed)'
            })
            continue

        # Create query
        query = f"""; Include base model
{smt_content}

; Query: Is {signal_name} always {expected_value}?
(assert (not (= {signal_name} {expected_value})))
(check-sat)
"""

        # Write query to temp file
        with tempfile.NamedTemporaryFile(mode='w', suffix='.smt2', delete=False) as f:
            f.write(query)
            query_file = f.name

        # Run Z3
        result = subprocess.run(
            ['z3', '-smt2', query_file],
            capture_output=True,
            text=True,
            timeout=30
        )

        # Clean up
        Path(query_file).unlink()

        # Parse result
        if 'unsat' in result.stdout.lower():
            status = 'CONSTANT'
            message = f'Provably constant {expected_value}'
        elif 'sat' in result.stdout.lower():
            status = 'VARIABLE'
            message = 'Can take different values (not constant)'
        else:
            status = 'UNKNOWN'
            message = f'Could not determine (Z3 output: {result.stdout.strip()})'

        results.append({
            'signal': signal_name,
            'description': description,
            'status': status,
            'message': message
        })

    return results

def main():
    if len(sys.argv) != 2:
        print("Usage: smt_check_rtl_signals.py <output_base>")
        print("")
        print("Example: smt_check_rtl_signals.py output/ibex_optimized")
        print("")
        print("Uses SMT to check which RTL signals are provably constant")
        print("Requires: yosys, z3")
        sys.exit(1)

    base_path = sys.argv[1]
    id_stage_modified = f"{base_path}_id_stage.sv"
    smt2_output = f"{base_path}_signals.smt2"

    if not Path(id_stage_modified).exists():
        print(f"ERROR: Modified ID stage not found: {id_stage_modified}")
        sys.exit(1)

    print("=" * 80)
    print(" " * 25 + "SMT-BASED RTL SIGNAL ANALYSIS")
    print("=" * 80)
    print()

    # Generate SMT2 model
    if not generate_smt_model(id_stage_modified, smt2_output):
        sys.exit(1)

    print()

    # Define signals to check
    signals_to_check = [
        ('mult_en_dec', '(_ bv0 1)', 'Multiplier enable from decoder'),
        ('div_en_dec', '(_ bv0 1)', 'Divider enable from decoder'),
        ('mult_sel_ex_o', '(_ bv0 1)', 'Multiplier select for EX stage'),
        ('div_sel_ex_o', '(_ bv0 1)', 'Divider select for EX stage'),
    ]

    # Check if Z3 is available
    try:
        subprocess.run(['z3', '--version'], capture_output=True, check=True)
    except (subprocess.CalledProcessError, FileNotFoundError):
        print("ERROR: Z3 not found. Please install Z3 SMT solver.")
        print("  Ubuntu: sudo apt install z3")
        print("  Or: https://github.com/Z3Prover/z3")
        sys.exit(1)

    # Check signals
    results = check_signal_with_z3(smt2_output, signals_to_check)

    # Report results
    print("RTL SIGNAL CONSTANCY REPORT")
    print("-" * 80)
    print()

    constant_signals = []
    variable_signals = []
    unknown_signals = []

    for result in results:
        symbol = "✓" if result['status'] == 'CONSTANT' else "✗"
        print(f"{symbol} {result['signal']}")
        print(f"  Description: {result['description']}")
        print(f"  Status: {result['status']}")
        print(f"  {result['message']}")
        print()

        if result['status'] == 'CONSTANT':
            constant_signals.append(result['signal'])
        elif result['status'] == 'VARIABLE':
            variable_signals.append(result['signal'])
        else:
            unknown_signals.append(result['signal'])

    # Summary
    print("-" * 80)
    print("SUMMARY")
    print("-" * 80)
    print(f"  Constant signals: {len(constant_signals)}/{len(results)}")
    print(f"  Variable signals: {len(variable_signals)}/{len(results)}")
    print(f"  Unknown/Not found: {len(unknown_signals)}/{len(results)}")
    print()

    if constant_signals:
        print("Dead code detected in:")
        for sig in constant_signals:
            print(f"  - {sig}")
        print()
        print("These signals are provably constant under your DSL constraints.")
        print("Consider removing associated logic or investigating why they're unused.")

    print()
    print(f"SMT2 model saved to: {smt2_output}")
    print("You can manually query it with: z3 -smt2 <query.smt2>")
    print()

if __name__ == '__main__':
    main()
