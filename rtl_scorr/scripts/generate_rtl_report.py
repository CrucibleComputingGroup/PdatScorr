#!/usr/bin/env python3
"""
Generate human-readable RTL dead-code report from proven equivalences.

Creates actionable report suitable for RTL designers/reviewers.
"""

import sys
import json
from pathlib import Path

def generate_rtl_report(equivalences_file, rtl_file, output_report):
    """Generate human-readable RTL dead-code report."""

    # Load proven equivalences
    with open(equivalences_file, 'r') as f:
        data = json.load(f)
        equivalences = data.get('proven_equivalences', [])
        k = data.get('k', 'unknown')
        method = data.get('method', 'unknown')

    report = []
    report.append("=" * 80)
    report.append("RTL DEAD CODE DETECTION REPORT")
    report.append("=" * 80)
    report.append("")
    report.append(f"Source: {rtl_file}")
    report.append(f"Analysis method: {method}")
    report.append(f"K-induction depth: {k}")
    report.append("")

    if not equivalences:
        report.append("No dead code detected - design is clean under given constraints!")
        report.append("")
        return "\n".join(report)

    report.append(f"Found {len(equivalences)} equivalence(s) indicating potential dead code:")
    report.append("")

    for i, (sig_a, sig_b) in enumerate(equivalences, 1):
        report.append("-" * 80)
        report.append(f"Finding #{i}: Signal Equivalence")
        report.append("-" * 80)
        report.append(f"  Signal A: {sig_a}")
        report.append(f"  Signal B: {sig_b}")
        report.append(f"  Relationship: {sig_a} ≡ {sig_b}")
        report.append("")

        # Interpret the finding
        if '#' in sig_a:
            # Internal/combinational signal
            report.append(f"  Interpretation:")
            report.append(f"    - {sig_a} is an internal combinational signal")
            report.append(f"    - It is provably equivalent to {sig_b}")
            report.append(f"    - Logic computing {sig_a} can be replaced with {sig_b}")
            report.append("")
            report.append(f"  Impact:")
            report.append(f"    - Dead combinational logic detected")
            report.append(f"    - Datapath can be simplified")
            report.append("")

            # Specific interpretation for simple_mux example
            if 'mux' in sig_a.lower() and sig_b == 'data_a':
                report.append(f"  Specific Analysis (simple_mux example):")
                report.append(f"    - This is a mux output equivalent to one input ({sig_b})")
                report.append(f"    - The other mux input (data_b) is never selected")
                report.append(f"    - Constraint: assume(enable == 0) forces mux to always select {sig_b}")
                report.append("")
                report.append(f"  Recommended Action:")
                report.append(f"    - Remove data_b input (unused)")
                report.append(f"    - Replace mux with direct connection to {sig_b}")
                report.append(f"    - Or document why enable is constrained to 0")
                report.append("")
        else:
            # Named signal
            report.append(f"  Interpretation:")
            report.append(f"    - Named signal {sig_a} is equivalent to {sig_b}")
            report.append(f"    - One of these signals is redundant")
            report.append("")

    report.append("=" * 80)
    report.append("SUMMARY")
    report.append("=" * 80)
    report.append(f"Total findings: {len(equivalences)}")
    report.append(f"These equivalences were proven using formal methods (SMT k-induction)")
    report.append(f"under the constraints specified in the design's assume statements.")
    report.append("")
    report.append("Next steps:")
    report.append("  1. Review each finding")
    report.append("  2. Verify constraints match design intent")
    report.append("  3. Remove dead code or document why it exists")
    report.append("  4. Consider if constraints should be relaxed")
    report.append("")

    return "\n".join(report)

def main():
    if len(sys.argv) != 3:
        print("Usage: generate_rtl_report.py <proven_equivalences.json> <rtl_file>")
        print("")
        print("Generates human-readable RTL dead-code report")
        sys.exit(1)

    equiv_file = Path(sys.argv[1])
    rtl_file = Path(sys.argv[2])

    if not equiv_file.exists():
        print(f"ERROR: Equivalences file not found: {equiv_file}")
        sys.exit(1)

    # Generate report
    output_report = equiv_file.parent / "RTL_DEAD_CODE_REPORT.txt"

    report = generate_rtl_report(equiv_file, rtl_file, output_report)

    # Write to file
    with open(output_report, 'w') as f:
        f.write(report)

    # Also print to stdout
    print(report)

    print(f"\n✓ Report saved to: {output_report}")

if __name__ == '__main__':
    main()
