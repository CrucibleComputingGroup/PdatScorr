#!/usr/bin/env python3
"""
ODC Analysis Tool: Find observability don't cares via error injection and bounded SEC

This tool:
1. Parses DSL to identify bits that should be constant
2. For each candidate bit:
   - Injects error (forces bit to constant) 
   - Synthesizes error-injected circuit
   - Runs bounded SEC vs baseline
3. Generates reports showing which bits are ODCs

Usage:
  ./scripts/odc_analysis.py my_rules.dsl \\
      --baseline-aig output/my_rules/ibex_optimized_post_abc.aig \\
      --output-dir output/my_rules/odc_analysis
"""

import sys
import argparse
import subprocess
from pathlib import Path
from typing import List, Optional

# Add project root to path
PROJECT_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(PROJECT_ROOT))

from odc.constraint_analyzer import ConstraintAnalyzer, ConstantBit
from odc.error_injector import ErrorInjector
from odc.sec_checker import SecChecker, SecResult
from odc.report_generator import ReportGenerator, OdcTestResult
from odc.synthesis import synthesize_error_injected_circuit


def find_ibex_root() -> Path:
    """Find Ibex core root directory."""
    # Try environment variable first
    import os
    if 'IBEX_ROOT' in os.environ:
        return Path(os.environ['IBEX_ROOT'])
    
    # Try common locations
    candidates = [
        PROJECT_ROOT.parent / "PdatCoreSim" / "cores" / "ibex",
        PROJECT_ROOT.parent / "CoreSim" / "cores" / "ibex",
    ]
    
    for candidate in candidates:
        if (candidate / "rtl" / "ibex_alu.sv").exists():
            return candidate
    
    raise FileNotFoundError(
        "Could not find Ibex core. Set IBEX_ROOT environment variable or "
        "place ibex at ../PdatCoreSim/cores/ibex/"
    )




def main():
    parser = argparse.ArgumentParser(
        description="ODC analysis via error injection and bounded SEC",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Basic usage with existing baseline
  %(prog)s my_rules.dsl --baseline-aig output/my_rules/ibex_optimized_post_abc.aig
  
  # Specify output directory and k-depth
  %(prog)s my_rules.dsl \\
      --baseline-aig baseline.aig \\
      --output-dir results/odc \\
      --k-depth 3
  
  # Analyze all fields, not just shamt
  %(prog)s my_rules.dsl --baseline-aig baseline.aig --scope all
"""
    )
    
    parser.add_argument("dsl_file", type=Path,
                       help="DSL file with instruction constraints")
    parser.add_argument("--baseline-aig", type=Path, required=True,
                       help="Baseline optimized AIGER file")
    parser.add_argument("--output-dir", type=Path,
                       default=Path("output/odc_analysis"),
                       help="Output directory (default: output/odc_analysis)")
    parser.add_argument("--scope", choices=["shamt", "all"], default="shamt",
                       help="Analysis scope: shamt only or all fields")
    parser.add_argument("--k-depth", type=int, default=2,
                       help="Bounded SEC induction depth (default: 2)")
    parser.add_argument("--config", type=Path, default=Path("configs/ibex.yaml"),
                       help="Core configuration file (default: configs/ibex.yaml)")
    parser.add_argument("--skip-synthesis", action="store_true",
                       help="Skip synthesis (for testing report generation)")
    
    args = parser.parse_args()
    
    # Validate inputs
    if not args.dsl_file.exists():
        print(f"ERROR: DSL file not found: {args.dsl_file}")
        return 1
    
    if not args.skip_synthesis and not args.baseline_aig.exists():
        print(f"ERROR: Baseline AIGER not found: {args.baseline_aig}")
        return 1
    
    # Load config to get core information
    if not args.config.exists():
        print(f"ERROR: Config file not found: {args.config}")
        return 1

    sys.path.insert(0, str(PROJECT_ROOT / "scripts"))
    from config_loader import ConfigLoader

    try:
        config = ConfigLoader.load_config(str(args.config))
        core_root = Path(config.synthesis.core_root_resolved)
        print(f"Using core: {config.core_name} at {core_root}")
    except Exception as e:
        print(f"ERROR: Failed to load config: {e}")
        return 1
    
    # Create output directories
    args.output_dir.mkdir(parents=True, exist_ok=True)
    error_injection_dir = args.output_dir / "error_injection"
    error_injection_dir.mkdir(exist_ok=True)
    sec_logs_dir = args.output_dir / "sec_logs"
    sec_logs_dir.mkdir(exist_ok=True)
    
    print("="*70)
    print("ODC Analysis: Error Injection + Bounded SEC")
    print("="*70)
    print(f"DSL file: {args.dsl_file}")
    print(f"Baseline: {args.baseline_aig}")
    print(f"Scope: {args.scope}")
    print(f"K-depth: {args.k_depth}")
    print(f"Output: {args.output_dir}")
    print()
    
    # Step 1: Analyze DSL to find constant bits
    print("[1/4] Analyzing DSL constraints...")
    analyzer = ConstraintAnalyzer(args.dsl_file)
    constant_bits = analyzer.get_candidate_odc_bits(args.scope)
    
    if not constant_bits:
        print("  No constant bits found - nothing to test")
        return 0
    
    print(f"  Found {len(constant_bits)} candidate ODC bits:")
    for cb in constant_bits:
        print(f"    {cb}")
    print()
    
    # Step 2: For each candidate, inject error and test
    print(f"[2/4] Testing {len(constant_bits)} candidates...")
    
    injector = ErrorInjector(core_root / "rtl")
    checker = SecChecker(conflict_limit=30000, timeout_sec=600)
    test_results = []
    
    for i, constant_bit in enumerate(constant_bits, 1):
        print(f"  [{i}/{len(constant_bits)}] Testing {constant_bit}")
        
        # Generate error-injected RTL
        try:
            error_rtl = injector.inject_constant_bit(
                constant_bit, 
                error_injection_dir,
                test_opposite=False  # Force to constraint-specified value
            )
            print(f"    Generated: {error_rtl.name}")
        except Exception as e:
            print(f"    ERROR: Injection failed: {e}")
            # Create dummy failed result
            from odc.sec_checker import SecStatus
            test_results.append(OdcTestResult(
                constant_bit,
                SecResult(SecStatus.ERROR, 0.0, abc_output=str(e))
            ))
            continue
        
        if args.skip_synthesis:
            # Create dummy result for testing
            print(f"    Skipping synthesis (--skip-synthesis)")
            from odc.sec_checker import SecStatus
            # Alternate between equivalent and not equivalent for testing
            status = SecStatus.EQUIVALENT if i % 2 == 0 else SecStatus.NOT_EQUIVALENT
            test_results.append(OdcTestResult(
                constant_bit,
                SecResult(status, 1.0 + i*0.1)
            ))
            continue
        
        # Synthesize error-injected circuit
        error_aig = synthesize_error_injected_circuit(
            error_rtl, args.dsl_file, error_injection_dir, args.config, args.k_depth
        )
        
        if error_aig is None:
            print(f"    ERROR: Synthesis failed or not implemented")
            from odc.sec_checker import SecStatus
            test_results.append(OdcTestResult(
                constant_bit,
                SecResult(SecStatus.ERROR, 0.0, abc_output="Synthesis failed")
            ))
            continue
        
        # Run bounded SEC
        print(f"    Running SEC (k={args.k_depth})...")
        sec_result = checker.check_equivalence(
            args.baseline_aig,
            error_aig,
            args.k_depth
        )
        
        print(f"    Result: {sec_result.status.value} ({sec_result.runtime_sec:.2f}s)")
        
        # Save SEC log
        log_file = sec_logs_dir / f"{constant_bit.field_name}_bit{constant_bit.bit_position}.log"
        log_file.write_text(sec_result.abc_output)
        
        test_results.append(OdcTestResult(constant_bit, sec_result))
        print()
    
    # Step 3: Generate reports
    print("[3/4] Generating reports...")
    generator = ReportGenerator(args.dsl_file, args.output_dir)
    generator.generate_reports(test_results)
    print()
    
    # Step 4: Summary
    print("[4/4] Summary")
    print("="*70)
    
    odc_count = sum(1 for r in test_results if r.is_odc)
    non_odc_count = len(test_results) - odc_count
    
    print(f"Total tests: {len(test_results)}")
    print(f"Confirmed ODCs: {odc_count}")
    print(f"Not ODCs: {non_odc_count}")
    print()
    
    if odc_count > 0:
        print("Confirmed ODC bits (can be tied to constants):")
        for result in test_results:
            if result.is_odc:
                cb = result.constant_bit
                print(f"  ✓ {cb.field_name}[{cb.bit_position}] = {cb.constant_value}")
    else:
        print("No ODCs confirmed.")
    
    print()
    print(f"Reports saved to: {args.output_dir}")
    print("="*70)
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
