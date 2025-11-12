#!/usr/bin/env python3
"""
Clean batch synthesis runner for PdatProject

Runs synth_core.sh on multiple DSL files in parallel and generates
a summary table showing Baseline vs Optimized vs Delta for:
- AND gate count (AIG)
- Tech-mapped area (SkyWater 130nm)
- Maximum frequency (Static Timing Analysis)
"""

import argparse
import json
import subprocess
import sys
from dataclasses import dataclass
from multiprocessing import Pool
from pathlib import Path
from typing import List, Optional
import re


@dataclass
class SynthesisMetrics:
    """Metrics extracted from a synthesis run."""
    name: str
    success: bool

    # AND gate counts (from AIGER)
    and_baseline: Optional[int] = None
    and_optimized: Optional[int] = None

    # Tech-mapped area (µm²)
    area_baseline: Optional[float] = None
    area_optimized: Optional[float] = None

    # Frequency (MHz)
    freq_baseline: Optional[float] = None
    freq_optimized: Optional[float] = None

    @property
    def and_delta(self) -> Optional[int]:
        if self.and_baseline is not None and self.and_optimized is not None:
            return self.and_optimized - self.and_baseline
        return None

    @property
    def and_delta_pct(self) -> Optional[float]:
        if self.and_baseline and self.and_delta is not None:
            return 100.0 * self.and_delta / self.and_baseline
        return None

    @property
    def area_delta(self) -> Optional[float]:
        if self.area_baseline is not None and self.area_optimized is not None:
            return self.area_optimized - self.area_baseline
        return None

    @property
    def area_delta_pct(self) -> Optional[float]:
        if self.area_baseline and self.area_delta is not None:
            return 100.0 * self.area_delta / self.area_baseline
        return None

    @property
    def freq_delta(self) -> Optional[float]:
        if self.freq_baseline is not None and self.freq_optimized is not None:
            return self.freq_optimized - self.freq_baseline
        return None

    @property
    def freq_delta_pct(self) -> Optional[float]:
        if self.freq_baseline and self.freq_delta is not None:
            return 100.0 * self.freq_delta / self.freq_baseline
        return None


def extract_and_gates(aig_file: Path) -> Optional[int]:
    """Extract AND gate count from AIGER file using ABC."""
    try:
        result = subprocess.run(
            ["abc", "-c", f"read_aiger {aig_file}; print_stats"],
            capture_output=True,
            text=True,
            timeout=10
        )
        match = re.search(r'and\s*=\s*(\d+)', result.stdout)
        return int(match.group(1)) if match else None
    except:
        return None


def extract_metrics(output_dir: Path, core_name: str) -> SynthesisMetrics:
    """Extract all metrics from a synthesis run output directory."""
    name = output_dir.name

    # Check if synthesis succeeded
    optimized_aig = output_dir / f"{core_name}_optimized_post_abc.aig"
    if not optimized_aig.exists():
        return SynthesisMetrics(name=name, success=False)

    metrics = SynthesisMetrics(name=name, success=True)

    # Extract AND gate counts
    # Use true baseline (unmodified core) if it exists
    true_baseline_aig = output_dir / f"{core_name}_optimized_baseline_yosys.aig"
    fallback_baseline_aig = output_dir / f"{core_name}_optimized_yosys.aig"

    if true_baseline_aig.exists():
        metrics.and_baseline = extract_and_gates(true_baseline_aig)
    elif fallback_baseline_aig.exists():
        metrics.and_baseline = extract_and_gates(fallback_baseline_aig)

    if optimized_aig.exists():
        metrics.and_optimized = extract_and_gates(optimized_aig)

    # Extract area
    area_baseline_file = output_dir / f"{core_name}_optimized_yosys_total_area.txt"
    if area_baseline_file.exists():
        try:
            metrics.area_baseline = float(area_baseline_file.read_text().strip())
        except:
            pass

    area_optimized_file = output_dir / f"{core_name}_optimized_total_area.txt"
    if area_optimized_file.exists():
        try:
            metrics.area_optimized = float(area_optimized_file.read_text().strip())
        except:
            pass

    # Extract frequency
    freq_baseline_file = output_dir / f"{core_name}_optimized_yosys_timing_metrics.json"
    if freq_baseline_file.exists():
        try:
            data = json.loads(freq_baseline_file.read_text())
            metrics.freq_baseline = data.get("max_frequency_mhz")
        except:
            pass

    freq_optimized_file = output_dir / f"{core_name}_optimized_timing_metrics.json"
    if freq_optimized_file.exists():
        try:
            data = json.loads(freq_optimized_file.read_text())
            metrics.freq_optimized = data.get("max_frequency_mhz")
        except:
            pass

    return metrics


def run_synthesis_job(args):
    """Run a single synthesis job (used by multiprocessing.Pool)."""
    dsl_file, output_base, core_name, synth_args, job_num, total = args

    name = dsl_file.stem
    output_dir = Path(output_base) / name
    output_dir.mkdir(parents=True, exist_ok=True)

    print(f"[{job_num}/{total}] Starting: {name}")

    try:
        # Build command
        cmd = ["./synth_core.sh"] + synth_args + [str(dsl_file), str(output_base)]

        # Run synthesis
        log_file = output_dir / "synthesis.log"
        with open(log_file, 'w') as f:
            result = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, text=True)

        if result.returncode == 0:
            print(f"[{job_num}/{total}] ✓ {name}")
            return True
        else:
            print(f"[{job_num}/{total}] ✗ {name} (see {log_file})")
            return False
    except Exception as e:
        print(f"[{job_num}/{total}] ✗ {name}: {e}")
        return False


def print_summary_table(results: List[SynthesisMetrics]):
    """Print formatted summary table with grouped columns."""
    print("\n" + "="*80)
    print("BATCH SYNTHESIS SUMMARY")
    print("="*80)

    # Header
    print(f"{'Design':<20} │ {'AND Gates (AIG)':<24} │ {'Area (µm²)':<24} │ {'Frequency (MHz)':<24}")
    print(f"{'':<20} │ {'Base   Opt    Δ (%)':<24} │ {'Base    Opt     Δ (%)':<24} │ {'Base   Opt    Δ (%)':<24}")
    print("─" * 20 + "─┼─" + "─" * 24 + "─┼─" + "─" * 24 + "─┼─" + "─" * 24)

    # Data rows
    for m in results:
        if not m.success:
            print(f"{m.name:<20} │ {'✗ FAILED':<72}")
            continue

        # Format AND gates
        and_str = format_metric_group(m.and_baseline, m.and_optimized, m.and_delta, m.and_delta_pct, int_vals=True)

        # Format area
        area_str = format_metric_group(m.area_baseline, m.area_optimized, m.area_delta, m.area_delta_pct)

        # Format frequency
        freq_str = format_metric_group(m.freq_baseline, m.freq_optimized, m.freq_delta, m.freq_delta_pct)

        print(f"{m.name:<20} │ {and_str:<24} │ {area_str:<24} │ {freq_str:<24}")

    print("─" * 80)

    # Summary stats
    passed = sum(1 for m in results if m.success)
    failed = len(results) - passed
    print(f"Summary: {passed} passed, {failed} failed")
    print("="*80)


def format_metric_group(baseline, optimized, delta, delta_pct, int_vals=False) -> str:
    """Format a metric group: baseline optimized delta(%)."""
    if baseline is None or optimized is None:
        return "N/A"

    if int_vals:
        b_str = f"{baseline:4d}"
        o_str = f"{optimized:4d}"
        d_str = f"{delta:+4d}" if delta is not None else "N/A"
    else:
        b_str = f"{baseline:6.1f}"
        o_str = f"{optimized:6.1f}"
        d_str = f"{delta:+6.1f}" if delta is not None else "N/A"

    if delta_pct is not None:
        pct_str = f"({delta_pct:+.1f}%)"
    else:
        pct_str = ""

    return f"{b_str} {o_str} {d_str:>7} {pct_str}"


def main():
    parser = argparse.ArgumentParser(
        description="Batch synthesis runner for multiple DSL files",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s --core serv --gates ./experiments/instruction_subsets/*.dsl
  %(prog)s --core ibex -j 8 --output results/ ../PdatRiscvDsl/workload/*.dsl
  %(prog)s --clean --core serv --gates experiments/instruction_subsets/
"""
    )

    parser.add_argument("dsl_files", nargs="+", type=Path,
                       help="DSL files or directories to synthesize")
    parser.add_argument("--core", default="ibex",
                       help="Core name (default: ibex)")
    parser.add_argument("--config", type=Path,
                       help="Core config file (overrides --core)")
    parser.add_argument("-o", "--output", type=Path, default=Path("output"),
                       help="Output base directory (default: output)")
    parser.add_argument("--gates", action="store_true",
                       help="Synthesize to gate level")
    parser.add_argument("--3stage", action="store_true",
                       help="Use 3-stage pipeline (Ibex only)")
    parser.add_argument("--abc-depth", type=int,
                       help="ABC k-induction depth")
    parser.add_argument("-j", "--jobs", type=int, default=4,
                       help="Max parallel jobs (default: 4)")
    parser.add_argument("--clean", action="store_true",
                       help="Automatically clean output directory without prompting")

    args = parser.parse_args()

    # Collect DSL files
    dsl_files = []
    for path in args.dsl_files:
        if path.is_dir():
            dsl_files.extend(sorted(path.glob("*.dsl")))
        elif path.suffix == ".dsl":
            dsl_files.append(path)
        else:
            print(f"WARNING: Skipping non-DSL file: {path}")

    if not dsl_files:
        print("ERROR: No DSL files found")
        return 1

    # Handle output directory cleanup
    if args.output.exists():
        if args.clean:
            print(f"Cleaning {args.output}...")
            import shutil
            shutil.rmtree(args.output)
        else:
            response = input(f"Output directory {args.output} exists. Clean it? [y/N]: ")
            if response.lower() == 'y':
                import shutil
                shutil.rmtree(args.output)
            else:
                print("Continuing with existing output directory (will overwrite individual runs)")

    args.output.mkdir(parents=True, exist_ok=True)

    # Build synthesis arguments
    synth_args = []
    if args.config:
        synth_args.extend(["--config", str(args.config)])
        # Extract core name from config for file naming
        import sys
        sys.path.insert(0, str(Path(__file__).parent / "scripts"))
        from config_loader import ConfigLoader
        config = ConfigLoader.load_config(str(args.config))
        core_name_for_files = config.core_name
    else:
        synth_args.extend(["--core", args.core])
        core_name_for_files = args.core

    if args.gates:
        synth_args.append("--gates")
    if getattr(args, '3stage', False):
        synth_args.append("--3stage")
    if args.abc_depth:
        synth_args.extend(["--abc-depth", str(args.abc_depth)])

    # Update args.core with the actual core name for metrics extraction
    args.core = core_name_for_files

    # Print configuration
    print("="*80)
    print("Batch Synthesis Configuration")
    print("="*80)
    print(f"Core:      {args.core}")
    print(f"DSL files: {len(dsl_files)}")
    print(f"Output:    {args.output}")
    print(f"Jobs:      {args.jobs}")
    print(f"Options:   {' '.join(synth_args)}")
    print()

    # Run synthesis jobs in parallel
    import time
    start_time = time.time()

    job_args = [
        (dsl, args.output, args.core, synth_args, i+1, len(dsl_files))
        for i, dsl in enumerate(dsl_files)
    ]

    with Pool(processes=args.jobs) as pool:
        pool.map(run_synthesis_job, job_args)

    elapsed = time.time() - start_time

    # Extract metrics from all results
    results = []
    for dsl in dsl_files:
        output_dir = args.output / dsl.stem
        metrics = extract_metrics(output_dir, args.core)
        results.append(metrics)

    # Print summary table
    print(f"\nTotal time: {elapsed:.1f}s\n")
    print_summary_table(results)

    return 0


if __name__ == "__main__":
    sys.exit(main())
