#!/usr/bin/env python3
"""
SEC Checker: Sequential Equivalence Checking using ABC

Performs bounded SEC using ABC's miter + SAT approach to verify if two
circuits are equivalent under given constraints.
"""

import subprocess
from pathlib import Path
from dataclasses import dataclass
from typing import Optional, Tuple
from enum import Enum


class SecStatus(Enum):
    """Result status of SEC check."""
    EQUIVALENT = "equivalent"
    NOT_EQUIVALENT = "not_equivalent"
    TIMEOUT = "timeout"
    ERROR = "error"
    UNKNOWN = "unknown"


@dataclass
class SecResult:
    """Result of SEC check."""
    status: SecStatus
    runtime_sec: float
    counterexample: Optional[str] = None
    abc_output: str = ""
    
    def __str__(self):
        status_str = self.status.value.upper()
        result = f"SEC Result: {status_str} ({self.runtime_sec:.2f}s)"
        if self.counterexample:
            result += f"\nCounterexample: {self.counterexample}"
        return result
    
    @property
    def is_equivalent(self) -> bool:
        """Check if circuits proven equivalent."""
        return self.status == SecStatus.EQUIVALENT


class SecChecker:
    """Performs bounded sequential equivalence checking using ABC."""
    
    def __init__(self, abc_path: str = "abc", 
                 conflict_limit: int = 30000,
                 timeout_sec: int = 600):
        """
        Initialize SEC checker.
        
        Args:
            abc_path: Path to ABC executable
            conflict_limit: SAT solver conflict limit
            timeout_sec: Timeout for SEC check in seconds
        """
        self.abc_path = abc_path
        self.conflict_limit = conflict_limit
        self.timeout_sec = timeout_sec
    
    def check_equivalence(self, baseline_aig: Path, modified_aig: Path,
                         k_depth: int = 2) -> SecResult:
        """
        Check if two circuits are equivalent using bounded SEC.
        
        Uses miter + bounded SAT with k-induction.
        
        Args:
            baseline_aig: Baseline AIGER file
            modified_aig: Modified (error-injected) AIGER file
            k_depth: Induction depth (should match pipeline depth)
            
        Returns:
            SecResult with status and details
        """
        import time
        start_time = time.time()
        
        try:
            # Create ABC command script
            abc_script = self._generate_sec_script(baseline_aig, modified_aig, k_depth)
            
            # Run ABC - use absolute paths or ensure we're in the right directory
            # Note: ABC script uses the Path objects which may be relative
            # Use stdout=PIPE, stderr=STDOUT to avoid buffering issues
            result = subprocess.run(
                [self.abc_path, "-c", abc_script],
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                timeout=self.timeout_sec
            )
            
            runtime = time.time() - start_time

            # Get output (stderr is merged into stdout)
            full_output = result.stdout

            # Debug: Uncomment to diagnose output capture issues
            # print(f"[DEBUG] ABC output: {len(full_output)} chars, exit={result.returncode}")
            # if len(full_output) < 500:
            #     print(f"[DEBUG] Full output: {repr(full_output[:200])}")

            # Parse ABC output to determine result
            status, counterexample = self._parse_abc_output(full_output)

            return SecResult(
                status=status,
                runtime_sec=runtime,
                counterexample=counterexample,
                abc_output=full_output
            )
            
        except subprocess.TimeoutExpired:
            runtime = time.time() - start_time
            return SecResult(
                status=SecStatus.TIMEOUT,
                runtime_sec=runtime,
                abc_output="ABC timeout"
            )
        except Exception as e:
            runtime = time.time() - start_time
            return SecResult(
                status=SecStatus.ERROR,
                runtime_sec=runtime,
                abc_output=str(e)
            )
    
    def _generate_sec_script(self, baseline_aig: Path, modified_aig: Path,
                            k_depth: int) -> str:
        """
        Generate ABC command script for bounded SEC.

        Args:
            baseline_aig: Baseline circuit
            modified_aig: Modified circuit
            k_depth: Induction depth

        Returns:
            ABC command string
        """
        # Use dsec for proper sequential equivalence checking with induction
        # -F sets the induction depth (k-BMC bound)
        # -v for verbose output
        # -n to match CIs/COs by name (not order) since circuits have same signal names
        # -r enables forward retiming (default=yes, helps with sequential optimization)

        # Note: If modified circuit has constraint outputs, remove them first
        # to ensure both circuits have the same number of outputs

        # Use absolute paths to ensure ABC can find files regardless of cwd
        baseline_abs = baseline_aig.absolute() if not baseline_aig.is_absolute() else baseline_aig
        modified_abs = modified_aig.absolute() if not modified_aig.is_absolute() else modified_aig

        # IMPORTANT: Use single-line command - multi-line scripts with comments cause ABC to truncate output
        script = f"read_aiger {baseline_abs}; read_aiger {modified_abs}; constr -r; dsec -F {k_depth} -v;"

        return script
    
    def _parse_abc_output(self, output: str) -> Tuple[SecStatus, Optional[str]]:
        """
        Parse ABC output to determine SEC result.

        Args:
            output: ABC stdout/stderr

        Returns:
            Tuple of (status, counterexample)
        """
        output_lower = output.lower()

        # Check for &cec specific outputs
        if "networks are equivalent" in output_lower:
            return SecStatus.EQUIVALENT, None

        if "networks are not equivalent" in output_lower or "not equivalent" in output_lower:
            # Try to extract which output differs
            cex = self._extract_counterexample(output)
            return SecStatus.NOT_EQUIVALENT, cex

        # Check for UNSAT (equivalent - from sat-based methods)
        if "unsat" in output_lower or "unsatisfiable" in output_lower:
            return SecStatus.EQUIVALENT, None

        # Check for SAT (not equivalent - counterexample exists)
        if "satisfiable" in output_lower or ("sat" in output_lower and "unsat" not in output_lower):
            # Try to extract counterexample
            cex = self._extract_counterexample(output)
            return SecStatus.NOT_EQUIVALENT, cex

        # Check for timeout
        if "timeout" in output_lower or "resource limit" in output_lower:
            return SecStatus.TIMEOUT, None

        # Check for errors
        if "error" in output_lower or "failed" in output_lower:
            return SecStatus.ERROR, None

        # Unknown result
        return SecStatus.UNKNOWN, None
    
    def _extract_counterexample(self, output: str) -> Optional[str]:
        """
        Extract counterexample from ABC output if available.
        
        Args:
            output: ABC output
            
        Returns:
            Counterexample string or None
        """
        # ABC SAT output format varies, try to extract useful info
        # Look for patterns like "Var 123 = 1"
        cex_lines = []
        for line in output.split('\n'):
            if 'Var' in line or 'Input' in line or 'PI' in line:
                cex_lines.append(line.strip())
        
        if cex_lines:
            return '\n'.join(cex_lines[:10])  # Limit to first 10 lines
        
        return None
    
    def check_miter_is_zero(self, miter_aig: Path) -> SecResult:
        """
        Check if a miter circuit always outputs zero (circuits equivalent).
        
        This is an alternative approach where the miter is pre-built.
        
        Args:
            miter_aig: Pre-built miter AIGER file
            
        Returns:
            SecResult
        """
        import time
        start_time = time.time()
        
        try:
            # ABC script to check if miter outputs are always 0
            script = f"""
read_aiger {miter_aig};
strash;
fraig -C {self.conflict_limit};
sat -C {self.conflict_limit} -v;
""".strip()
            
            result = subprocess.run(
                [self.abc_path, "-c", script],
                capture_output=True,
                text=True,
                timeout=self.timeout_sec
            )
            
            runtime = time.time() - start_time
            status, cex = self._parse_abc_output(result.stdout + result.stderr)
            
            return SecResult(
                status=status,
                runtime_sec=runtime,
                counterexample=cex,
                abc_output=result.stdout + result.stderr
            )
            
        except subprocess.TimeoutExpired:
            runtime = time.time() - start_time
            return SecResult(
                status=SecStatus.TIMEOUT,
                runtime_sec=runtime
            )
        except Exception as e:
            runtime = time.time() - start_time
            return SecResult(
                status=SecStatus.ERROR,
                runtime_sec=runtime,
                abc_output=str(e)
            )


def main():
    """CLI interface for testing SEC checker."""
    import argparse
    
    parser = argparse.ArgumentParser(description="Run bounded SEC with ABC")
    parser.add_argument("baseline_aig", type=Path, help="Baseline AIGER file")
    parser.add_argument("modified_aig", type=Path, help="Modified AIGER file")
    parser.add_argument("--k-depth", type=int, default=2,
                       help="Induction depth (default: 2)")
    parser.add_argument("--conflict-limit", type=int, default=30000,
                       help="SAT conflict limit (default: 30000)")
    parser.add_argument("--timeout", type=int, default=600,
                       help="Timeout in seconds (default: 600)")
    parser.add_argument("--abc", default="abc", help="Path to ABC executable")
    
    args = parser.parse_args()
    
    if not args.baseline_aig.exists():
        print(f"ERROR: Baseline file not found: {args.baseline_aig}")
        return 1
    
    if not args.modified_aig.exists():
        print(f"ERROR: Modified file not found: {args.modified_aig}")
        return 1
    
    checker = SecChecker(
        abc_path=args.abc,
        conflict_limit=args.conflict_limit,
        timeout_sec=args.timeout
    )
    
    print(f"Running bounded SEC (k={args.k_depth})...")
    print(f"  Baseline: {args.baseline_aig}")
    print(f"  Modified: {args.modified_aig}")
    print()
    
    result = checker.check_equivalence(args.baseline_aig, args.modified_aig, args.k_depth)
    
    print(result)
    print()
    
    if result.status == SecStatus.EQUIVALENT:
        print("✓ Circuits are EQUIVALENT - This is an ODC!")
        return 0
    elif result.status == SecStatus.NOT_EQUIVALENT:
        print("✗ Circuits are NOT equivalent - NOT an ODC")
        return 1
    else:
        print(f"? SEC result: {result.status.value}")
        return 2


if __name__ == "__main__":
    import sys
    sys.exit(main())
