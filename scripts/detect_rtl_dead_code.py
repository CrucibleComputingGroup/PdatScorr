#!/usr/bin/env python3
"""
Analyze ABC optimization results and report RTL-level dead code.

This script takes the pre/post ABC AIGER files and generates a report
showing which RTL signals became constant or unused.
"""

import sys
import re
import subprocess
from pathlib import Path

def analyze_aiger_stats(pre_aig_path, post_aig_path):
    """Compare pre/post ABC AIGER files to see what was optimized."""

    # Read AIGER files to get statistics
    def get_aiger_stats(aig_path):
        """Run ABC to get AIGER statistics."""
        result = subprocess.run(
            ['abc', '-c', f'read_aiger {aig_path}; print_stats'],
            capture_output=True, text=True
        )

        # Parse output for statistics
        # Format: "i/o = 1338/  442(c=11)  lat =  942  and =  26178"
        match = re.search(r'lat\s+=\s+(\d+)\s+and\s+=\s+(\d+)', result.stdout)
        if match:
            return {
                'latches': int(match.group(1)),
                'ands': int(match.group(2))
            }
        return None

    pre_stats = get_aiger_stats(pre_aig_path)
    post_stats = get_aiger_stats(post_aig_path)

    if not pre_stats or not post_stats:
        print("ERROR: Could not parse AIGER statistics")
        return None

    return {
        'latches_removed': pre_stats['latches'] - post_stats['latches'],
        'ands_removed': pre_stats['ands'] - post_stats['ands'],
        'latch_reduction_pct': 100.0 * (pre_stats['latches'] - post_stats['latches']) / pre_stats['latches'],
        'and_reduction_pct': 100.0 * (pre_stats['ands'] - post_stats['ands']) / pre_stats['ands'],
        'pre': pre_stats,
        'post': post_stats
    }

def generate_yosys_equiv_script(pre_aig, post_aig, output_report):
    """Generate Yosys script to find constant signals."""

    script = f"""# Analyze which signals became constant after ABC optimization

# Read optimized AIGER
read_aiger {post_aig}

# Analyze for constant signals
# Look for signals tied to 0 or 1
select -set const0 t:$_BUF_ %i i:A=1'0 %i
select -set const1 t:$_BUF_ %i i:A=1'1 %i

# Print constant signal report
echo "=== Constant Signals (tied to 0) ==="
select @const0
show -format dot -prefix {output_report}_const0
ls @const0

echo "=== Constant Signals (tied to 1) ==="
select @const1
show -format dot -prefix {output_report}_const1
ls @const1

# Find unused signals (drive nothing)
echo "=== Unused Signals ==="
select w:* %ci %ci %D
ls

# Statistics comparison would require loading both AIGers
# For now, just show post-optimization statistics
stat
"""
    return script

def run_yosys_analysis(script_path):
    """Run Yosys with the analysis script."""
    result = subprocess.run(
        ['yosys', '-s', script_path],
        capture_output=True, text=True
    )
    return result.stdout, result.stderr

def parse_abc_log_for_constraints(abc_log_path):
    """Extract information about which constraints were used."""

    with open(abc_log_path, 'r') as f:
        log = f.read()

    # Find constraint statistics
    # "Total cones = 28458. Constraint cones = 481. (1.69 %)"
    match = re.search(r'Constraint cones\s+=\s+(\d+)\.\s+\(\s*([\d.]+)\s*%\)', log)
    if match:
        return {
            'constraint_cones': int(match.group(1)),
            'constraint_percentage': float(match.group(2))
        }

    # Also find removed equivalences
    # "Total equivs = 9911. Removed equivs = 146. (1.47 %)"
    match = re.search(r'Removed equivs\s+=\s+(\d+)\.\s+\(\s*([\d.]+)\s*%\)', log)
    if match:
        return {
            'removed_equivs': int(match.group(1)),
            'removed_equivs_percentage': float(match.group(2))
        }

    return {}

def main():
    if len(sys.argv) != 2:
        print("Usage: detect_rtl_dead_code.py <output_base_path>")
        print("")
        print("Example: detect_rtl_dead_code.py output/ibex_optimized")
        print("")
        print("Analyzes ABC optimization results and reports RTL-level dead code")
        sys.exit(1)

    base_path = sys.argv[1]
    pre_aig = f"{base_path}_pre_abc.aig"
    post_aig = f"{base_path}_post_abc.aig"
    abc_log = f"{base_path}_abc.log"

    # Check files exist
    for path in [pre_aig, post_aig]:
        if not Path(path).exists():
            print(f"ERROR: File not found: {path}")
            sys.exit(1)

    print("=" * 70)
    print("RTL DEAD CODE DETECTION REPORT")
    print("=" * 70)
    print()

    # Analyze AIGER statistics
    print("Analyzing optimization results...")
    stats = analyze_aiger_stats(pre_aig, post_aig)

    if stats:
        print(f"\n{'OPTIMIZATION SUMMARY':^70}")
        print("-" * 70)
        print(f"  Latches: {stats['pre']['latches']:,} → {stats['post']['latches']:,} "
              f"({stats['latches_removed']:,} removed, {stats['latch_reduction_pct']:.1f}%)")
        print(f"  ANDs:    {stats['pre']['ands']:,} → {stats['post']['ands']:,} "
              f"({stats['ands_removed']:,} removed, {stats['and_reduction_pct']:.1f}%)")
        print()

    # Analyze constraint usage
    if Path(abc_log).exists():
        constraint_info = parse_abc_log_for_constraints(abc_log)
        if constraint_info:
            print(f"{'CONSTRAINT IMPACT':^70}")
            print("-" * 70)
            for key, value in constraint_info.items():
                print(f"  {key}: {value}")
            print()

    # High-level interpretation
    print(f"{'INTERPRETATION':^70}")
    print("-" * 70)

    if stats['latch_reduction_pct'] > 5:
        print(f"  ⚠  {stats['latch_reduction_pct']:.1f}% of state removed")
        print(f"     → {stats['latches_removed']} sequential elements are provably unused")
        print(f"     → May indicate dead state machine states or unused registers")
        print()

    if stats['and_reduction_pct'] > 30:
        print(f"  ⚠  {stats['and_reduction_pct']:.1f}% of logic removed")
        print(f"     → Significant dead combinational logic detected")
        print(f"     → May indicate:")
        print(f"       - Unreachable decode paths")
        print(f"       - Unused functional units")
        print(f"       - Overly defensive error handling")
        print()

    if stats['and_reduction_pct'] < 10:
        print(f"  ✓  Only {stats['and_reduction_pct']:.1f}% logic removed")
        print(f"     → Design is well-optimized for given constraints")
        print(f"     → Minimal dead code detected")
        print()

    print("-" * 70)
    print("\nNOTE: This analysis is based on the constraints in your DSL file.")
    print("Dead code detection is relative to those constraints.")
    print()
    print("To get RTL signal names, use:")
    print(f"  yosys -p 'read_aiger {post_aig}; stat; show -format dot -prefix dead_code'")
    print()

if __name__ == '__main__':
    main()
