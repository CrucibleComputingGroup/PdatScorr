#!/usr/bin/env python3
"""
Generate RTL-level dead code report from synthesis results.

Analyzes synthesis logs and AIGER files to identify which RTL components
became dead or constant due to instruction constraints.
"""

import sys
import re
from pathlib import Path

def analyze_synthesis_log(yosys_log_path):
    """Parse Yosys log to find RTL signals and modules."""

    with open(yosys_log_path, 'r') as f:
        log = f.read()

    findings = {
        'modules_compiled': [],
        'warnings': [],
        'rtl_signals': []
    }

    # Find compiled modules
    for match in re.finditer(r'Compile module "work@([\w_]+)"', log):
        findings['modules_compiled'].append(match.group(1))

    return findings

def analyze_abc_log(abc_log_path):
    """Parse ABC log for optimization details."""

    with open(abc_log_path, 'r') as f:
        log = f.read()

    findings = {}

    # Extract key statistics
    # "NBeg = 26178. NEnd = 13591. (Gain =  48.08 %)."
    match = re.search(r'NBeg\s*=\s*(\d+)\.\s*NEnd\s*=\s*(\d+)\.\s*\(Gain\s*=\s*([\d.]+)', log)
    if match:
        nbeg = int(match.group(1))
        nend = int(match.group(2))
        gain_pct = float(match.group(3))
        findings['and_gates'] = {
            'before': nbeg,
            'after': nend,
            'removed': nbeg - nend,
            'reduction_pct': gain_pct
        }

    # Latches
    match = re.search(r'RBeg\s*=\s*(\d+)\.\s*REnd\s*=\s*(\d+)\.\s*\(Gain\s*=\s*([\d.]+)', log)
    if match:
        rbeg = int(match.group(1))
        rend = int(match.group(2))
        gain_pct = float(match.group(3))
        findings['latches'] = {
            'before': rbeg,
            'after': rend,
            'removed': rbeg - rend,
            'reduction_pct': gain_pct
        }

    # Constraint usage
    match = re.search(r'Removed equivs\s*=\s*(\d+)\.\s*\(\s*([\d.]+)\s*%\)', log)
    if match:
        findings['removed_equivs'] = int(match.group(1))
        findings['removed_equivs_pct'] = float(match.group(2))

    # Failed outputs (saturation in early frames)
    failed_outputs = re.findall(r'output (\d+) failed in frame (\d+)', log)
    if failed_outputs:
        findings['failed_outputs'] = len(failed_outputs)

    return findings

def infer_rtl_components(abc_findings, dsl_content):
    """Infer which RTL components were affected based on constraints."""

    affected_components = []

    # Parse DSL to see what was constrained
    has_mul = 'MUL' in dsl_content
    has_div = 'DIV' in dsl_content or 'REM' in dsl_content
    has_reg_constraint = 'require_registers' in dsl_content

    # Infer likely RTL impact
    if has_mul or has_div:
        affected_components.append({
            'module': 'ibex_multdiv_fast / ibex_multdiv_slow',
            'likely_impact': 'Multiplier/Divider datapath and state machine',
            'evidence': f"{abc_findings.get('removed_equivs', 0)} equivalences removed via constraints"
        })

        affected_components.append({
            'module': 'ibex_decoder',
            'signal': 'mult_en_dec, div_en_dec',
            'likely_impact': 'Decoder outputs tied to constant 0',
            'evidence': 'M-extension instructions outlawed'
        })

        affected_components.append({
            'module': 'ibex_ex_block',
            'signal': 'result mux selection',
            'likely_impact': 'Result mux always selects ALU path',
            'evidence': 'Mult/Div results never used'
        })

    if has_reg_constraint:
        match = re.search(r'require_registers\s+[\w-]+(\d+)', dsl_content)
        if match:
            max_reg = int(match.group(1))
            num_unused = 31 - max_reg
            affected_components.append({
                'module': 'ibex_register_file_ff',
                'likely_impact': f'~{num_unused} register entries unused',
                'evidence': f'Register constraint to x0-x{max_reg}'
            })

    latch_removed = abc_findings.get('latches', {}).get('removed', 0)
    if latch_removed > 100:
        affected_components.append({
            'module': 'ibex_multdiv_fast (FSM)',
            'likely_impact': f'~{latch_removed} state bits removed (FSM states unused)',
            'evidence': 'Large latch reduction'
        })

    return affected_components

def main():
    if len(sys.argv) not in [2, 3]:
        print("Usage: rtl_dead_code_report.py <output_base> [dsl_file]")
        print("")
        print("Example: rtl_dead_code_report.py output/ibex_optimized dsls/example_outlawed.dsl")
        print("")
        print("Generates RTL-level dead code report from synthesis results")
        sys.exit(1)

    base_path = sys.argv[1]
    dsl_path = sys.argv[2] if len(sys.argv) == 3 else None

    abc_log = f"{base_path}_abc.log"
    yosys_log = f"{base_path}_yosys.log"

    # Check files exist
    if not Path(abc_log).exists():
        print(f"ERROR: ABC log not found: {abc_log}")
        sys.exit(1)

    # Read DSL if provided
    dsl_content = ""
    if dsl_path and Path(dsl_path).exists():
        with open(dsl_path, 'r') as f:
            dsl_content = f.read()

    print("=" * 80)
    print(" " * 20 + "RTL DEAD CODE ANALYSIS REPORT")
    print("=" * 80)
    print()

    # Analyze ABC optimization
    abc_findings = analyze_abc_log(abc_log)

    # Summary
    print("OPTIMIZATION SUMMARY")
    print("-" * 80)
    if 'and_gates' in abc_findings:
        ag = abc_findings['and_gates']
        print(f"  AND Gates:  {ag['before']:,} → {ag['after']:,}  "
              f"({ag['removed']:,} removed, {ag['reduction_pct']:.1f}%)")

    if 'latches' in abc_findings:
        lt = abc_findings['latches']
        print(f"  Latches:    {lt['before']:,} → {lt['after']:,}  "
              f"({lt['removed']:,} removed, {lt['reduction_pct']:.1f}%)")

    if 'removed_equivs' in abc_findings:
        print(f"  Constraint-enabled equivalences: {abc_findings['removed_equivs']} "
              f"({abc_findings['removed_equivs_pct']:.2f}%)")

    print()

    # Infer RTL impact
    if dsl_content:
        components = infer_rtl_components(abc_findings, dsl_content)

        if components:
            print("LIKELY RTL COMPONENTS AFFECTED")
            print("-" * 80)
            for i, comp in enumerate(components, 1):
                print(f"\n{i}. {comp.get('module', 'Unknown')}")
                if 'signal' in comp:
                    print(f"   Signal: {comp['signal']}")
                print(f"   Impact: {comp['likely_impact']}")
                print(f"   Evidence: {comp['evidence']}")
            print()

    # Interpretation
    print("INTERPRETATION")
    print("-" * 80)

    if abc_findings.get('latches', {}).get('reduction_pct', 0) > 20:
        removed = abc_findings['latches']['removed']
        pct = abc_findings['latches']['reduction_pct']
        print(f"  ⚠  {pct:.1f}% of sequential state removed ({removed} latches)")
        print(f"     → Significant state machine optimization")
        print(f"     → Likely: FSM states unreachable under constraints")
        print(f"     → Check: Multiplier/Divider state machines")
        print()

    if abc_findings.get('and_gates', {}).get('reduction_pct', 0) > 50:
        removed = abc_findings['and_gates']['removed']
        pct = abc_findings['and_gates']['reduction_pct']
        print(f"  ⚠  {pct:.1f}% of combinational logic removed ({removed:,} ANDs)")
        print(f"     → Major decode/datapath simplification")
        print(f"     → Likely: Entire functional units unused")
        print(f"     → Check: Multiplier/Divider datapaths, unused ALU ops")
        print()

    if abc_findings.get('removed_equivs', 0) > 100:
        print(f"  ✓  {abc_findings['removed_equivs']} constraint-enabled equivalences found")
        print(f"     → Constraints were highly effective")
        print(f"     → Deep propagation through circuit")
        print()

    print("-" * 80)
    print("\nNOTE: This report infers RTL impact from AIG-level optimization.")
    print("For exact RTL signal names, examine:")
    print(f"  - Yosys log: {yosys_log}")
    print(f"  - ABC log: {abc_log}")
    print(f"\nTo see which specific signals are constant, you would need to:")
    print(f"  1. Preserve RTL names through synthesis (use -keep_hierarchy)")
    print(f"  2. Read optimized AIGER back into Yosys")
    print(f"  3. Compare signal values with original design")
    print()

if __name__ == '__main__':
    main()
