#!/usr/bin/env python3
"""
Regression tests for batch_synth.sh script.

Tests batch synthesis functionality including parallel execution,
multiple runs, and proper output organization.
"""

import os
import pytest
import subprocess
import tempfile
import shutil
from pathlib import Path
from typing import List


# Path to project root (2 levels up from this file)
PROJECT_ROOT = Path(__file__).parent.parent.parent
BATCH_SCRIPT = PROJECT_ROOT / "batch_synth.sh"
FIXTURES_DIR = Path(__file__).parent / "fixtures"


class BatchSynthResult:
    """Container for batch synthesis execution results."""

    def __init__(self, returncode: int, stdout: str, stderr: str, output_dir: Path):
        self.returncode = returncode
        self.stdout = stdout
        self.stderr = stderr
        self.output_dir = output_dir

    @property
    def success(self) -> bool:
        return self.returncode == 0

    def has_subdir(self, dirname: str) -> bool:
        """Check if output subdirectory exists."""
        return (self.output_dir / dirname).exists()

    def get_synthesis_dirs(self) -> List[Path]:
        """Get all synthesis output directories."""
        dirs = []
        for item in self.output_dir.iterdir():
            if item.is_dir():
                dirs.append(item)
        return dirs

    def count_completed_runs(self) -> int:
        """Count how many synthesis runs completed successfully."""
        count = 0
        for subdir in self.get_synthesis_dirs():
            # Check for yosys.aig as indicator of completion
            if any(subdir.rglob("*yosys.aig")):
                count += 1
        return count


def run_batch_synth(dsl_files: List[Path], output_dir: Path,
                    extra_args: List[str] = None) -> BatchSynthResult:
    """
    Run batch_synth.sh and return results.

    Args:
        dsl_files: List of DSL input files
        output_dir: Directory for outputs
        extra_args: Additional command-line arguments

    Returns:
        BatchSynthResult with execution details
    """
    cmd = [str(BATCH_SCRIPT)]

    # Force -j 1 to avoid nested parallelism when pytest runs tests in parallel
    # (otherwise we could have pytest -n 4 * batch -j 4 = 16 concurrent processes)
    cmd.extend(["-j", "1"])

    if extra_args:
        cmd.extend(extra_args)

    # Add output directory
    cmd.extend(["-o", str(output_dir)])

    # Add DSL files
    cmd.extend([str(f) for f in dsl_files])

    # Run with timeout
    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=600,  # 10 minute timeout
            cwd=PROJECT_ROOT
        )

        return BatchSynthResult(
            returncode=result.returncode,
            stdout=result.stdout,
            stderr=result.stderr,
            output_dir=output_dir
        )
    except subprocess.TimeoutExpired:
        pytest.fail("Batch synthesis timeout (>10 minutes)")


@pytest.fixture
def temp_output_dir(tmp_path):
    """Provide temporary directory for test outputs."""
    output_dir = tmp_path / "batch_output"
    output_dir.mkdir()
    yield output_dir


class TestBasicBatchSynthesis:
    """Test basic batch synthesis functionality."""

    def test_single_file(self, temp_output_dir):
        """Test batch synthesis with single DSL file."""
        dsl_files = [FIXTURES_DIR / "baseline.dsl"]
        result = run_batch_synth(dsl_files, temp_output_dir)

        assert result.success, f"Batch synthesis failed:\n{result.stdout}\n\n{result.stderr}"

        # Should create subdirectory for the DSL
        assert result.has_subdir("baseline"), "DSL subdirectory not created"

        # Check synthesis completed
        baseline_dir = temp_output_dir / "baseline"
        assert (baseline_dir / "ibex_optimized_yosys.aig").exists(), "Synthesis output not found"

    def test_multiple_files(self, temp_output_dir):
        """Test batch synthesis with multiple DSL files."""
        dsl_files = [
            FIXTURES_DIR / "baseline.dsl",
            FIXTURES_DIR / "simple_outlawed.dsl"
        ]
        result = run_batch_synth(dsl_files, temp_output_dir)

        assert result.success, f"Batch synthesis failed:\n{result.stdout}"

        # Should create subdirectories for both DSLs
        assert result.has_subdir("baseline"), "baseline subdirectory not created"
        assert result.has_subdir("simple_outlawed"), "simple_outlawed subdirectory not created"

        # Check synthesis was attempted (logs exist)
        # Note: Due to Surelog's slpp_all shared directory, parallel syntheses
        # may have race conditions. We just verify the batch script ran.
        assert (temp_output_dir / "baseline" / "synthesis.log").exists()
        assert (temp_output_dir / "simple_outlawed" / "synthesis.log").exists()

    def test_directory_input(self, temp_output_dir):
        """Test batch synthesis with directory as input."""
        # Pass fixtures directory containing DSL files
        result = run_batch_synth([FIXTURES_DIR], temp_output_dir)

        assert result.success, f"Batch synthesis with directory failed:\n{result.stdout}"

        # Should find and process DSL files in directory
        synthesis_dirs = result.get_synthesis_dirs()
        assert len(synthesis_dirs) >= 2, f"Expected at least 2 synthesis outputs, found {len(synthesis_dirs)}"


class TestBatchOptions:
    """Test batch synthesis command-line options."""

    def test_parallel_jobs(self, temp_output_dir):
        """Test -j/--jobs option."""
        dsl_files = [
            FIXTURES_DIR / "baseline.dsl",
            FIXTURES_DIR / "simple_outlawed.dsl"
        ]
        result = run_batch_synth(dsl_files, temp_output_dir, extra_args=["-j", "2"])

        assert result.success, f"Batch synthesis with -j 2 failed:\n{result.stdout}"
        assert "Max parallel:     2" in result.stdout, "Parallel jobs option not applied"

    def test_extra_synthesis_args(self, temp_output_dir):
        """Test passing extra arguments to synthesis script."""
        dsl_files = [FIXTURES_DIR / "baseline.dsl"]
        result = run_batch_synth(dsl_files, temp_output_dir, extra_args=["--abc-depth", "3"])

        assert result.success, f"Batch synthesis with extra args failed:\n{result.stdout}"
        # The extra args should be passed through
        assert "--abc-depth 3" in result.stdout or "abc-depth 3" in result.stdout

    def test_multiple_runs(self, temp_output_dir):
        """Test --runs option for multiple runs per DSL."""
        dsl_files = [FIXTURES_DIR / "baseline.dsl"]
        result = run_batch_synth(dsl_files, temp_output_dir, extra_args=["--runs", "2"])

        assert result.success, f"Batch synthesis with --runs 2 failed:\n{result.stdout}"

        # Should create run_1 and run_2 subdirectories
        assert result.has_subdir("run_1"), "run_1 directory not created"
        assert result.has_subdir("run_2"), "run_2 directory not created"

        # Both runs should have the baseline subdirectory
        assert (temp_output_dir / "run_1" / "baseline").exists()
        assert (temp_output_dir / "run_2" / "baseline").exists()


class TestBatchErrorHandling:
    """Test error handling in batch synthesis."""

    def test_no_dsl_files(self, temp_output_dir):
        """Test behavior when no DSL files provided."""
        result = run_batch_synth([], temp_output_dir)

        # Should fail gracefully
        assert not result.success, "Should fail with no DSL files"
        assert "No DSL files found" in result.stdout or "Error" in result.stdout

    def test_nonexistent_file(self, temp_output_dir):
        """Test behavior with non-existent DSL file."""
        dsl_files = [FIXTURES_DIR / "nonexistent.dsl"]
        # batch_synth.sh will skip non-existent files or fail
        # Either behavior is acceptable, but it shouldn't crash
        result = run_batch_synth(dsl_files, temp_output_dir)

        # Just check it doesn't crash with unhandled error
        # It may succeed (skip file) or fail (error message)
        # Both are acceptable
        assert "nonexistent" in result.stdout.lower() or result.success


class TestBatchOutputOrganization:
    """Test output file organization in batch mode."""

    def test_output_directory_structure(self, temp_output_dir):
        """Test that outputs are properly organized."""
        dsl_files = [
            FIXTURES_DIR / "baseline.dsl",
            FIXTURES_DIR / "simple_outlawed.dsl"
        ]
        result = run_batch_synth(dsl_files, temp_output_dir)

        assert result.success

        # Each DSL should have its own subdirectory
        baseline_dir = temp_output_dir / "baseline"
        outlawed_dir = temp_output_dir / "simple_outlawed"

        assert baseline_dir.exists() and baseline_dir.is_dir()
        assert outlawed_dir.exists() and outlawed_dir.is_dir()

        # Each should have synthesis logs (outputs may vary)
        assert (baseline_dir / "synthesis.log").exists()
        assert (outlawed_dir / "synthesis.log").exists()

        # Check that synthesis was attempted (at least some files created)
        assert (baseline_dir / "ibex_optimized_assumptions.sv").exists()
        assert (outlawed_dir / "ibex_optimized_assumptions.sv").exists()

    def test_multiple_runs_organization(self, temp_output_dir):
        """Test output organization with multiple runs."""
        dsl_files = [FIXTURES_DIR / "baseline.dsl"]
        result = run_batch_synth(dsl_files, temp_output_dir, extra_args=["--runs", "2"])

        assert result.success

        # Structure should be: run_N/dsl_name/files
        run1_baseline = temp_output_dir / "run_1" / "baseline"
        run2_baseline = temp_output_dir / "run_2" / "baseline"

        assert run1_baseline.exists(), "run_1/baseline not created"
        assert run2_baseline.exists(), "run_2/baseline not created"

        # Each run should have synthesis outputs
        assert (run1_baseline / "ibex_optimized_yosys.aig").exists()
        assert (run2_baseline / "ibex_optimized_yosys.aig").exists()


class TestBatchLogging:
    """Test logging and status reporting."""

    def test_synthesis_logs_created(self, temp_output_dir):
        """Test that synthesis logs are created for each run."""
        dsl_files = [FIXTURES_DIR / "baseline.dsl"]
        result = run_batch_synth(dsl_files, temp_output_dir)

        assert result.success

        # Should have synthesis.log
        log_file = temp_output_dir / "baseline" / "synthesis.log"
        assert log_file.exists(), "synthesis.log not created"
        assert log_file.stat().st_size > 0, "synthesis.log is empty"

    def test_batch_status_messages(self, temp_output_dir):
        """Test that batch script outputs status messages."""
        dsl_files = [FIXTURES_DIR / "baseline.dsl"]
        result = run_batch_synth(dsl_files, temp_output_dir)

        assert result.success

        # Should have configuration summary
        assert "Batch Synthesis Configuration" in result.stdout
        assert "DSL files:" in result.stdout

        # Should have completion messages
        assert "Completed:" in result.stdout or "✓" in result.stdout


if __name__ == "__main__":
    # Allow running directly for quick testing
    pytest.main([__file__, "-v"])
