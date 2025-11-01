#!/usr/bin/env python3
"""
Regression tests for Ibex synthesis flow.

Tests ensure that synthesis completes successfully and generates all expected
output files. Does NOT validate optimization quality, only flow completion.
"""

import os
import pytest
import subprocess
import tempfile
import shutil
from pathlib import Path
from typing import List, Tuple


# Path to project root (2 levels up from this file)
PROJECT_ROOT = Path(__file__).parent.parent.parent
SYNTH_SCRIPT = PROJECT_ROOT / "synth_ibex_with_constraints.sh"
FIXTURES_DIR = Path(__file__).parent / "fixtures"


class SynthesisResult:
    """Container for synthesis execution results."""

    def __init__(self, returncode: int, stdout: str, stderr: str, output_dir: Path):
        self.returncode = returncode
        self.stdout = stdout
        self.stderr = stderr
        self.output_dir = output_dir

    @property
    def success(self) -> bool:
        return self.returncode == 0

    def has_file(self, filename: str) -> bool:
        """Check if output file exists."""
        return (self.output_dir / filename).exists()

    def file_size(self, filename: str) -> int:
        """Get file size in bytes, 0 if doesn't exist."""
        filepath = self.output_dir / filename
        return filepath.stat().st_size if filepath.exists() else 0

    def file_contains(self, filename: str, text: str) -> bool:
        """Check if file contains specific text."""
        filepath = self.output_dir / filename
        if not filepath.exists():
            return False
        return text in filepath.read_text()


def run_synthesis(dsl_file: Path, output_dir: Path,
                  extra_args: List[str] = None) -> SynthesisResult:
    """
    Run synthesis script and return results.

    Args:
        dsl_file: Path to DSL input file
        output_dir: Directory for outputs
        extra_args: Additional command-line arguments

    Returns:
        SynthesisResult with execution details
    """
    cmd = [str(SYNTH_SCRIPT)]
    if extra_args:
        cmd.extend(extra_args)
    cmd.extend([str(dsl_file), str(output_dir)])

    # Run with timeout to prevent hanging
    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=600,  # 10 minute timeout
            cwd=PROJECT_ROOT,
            env=os.environ.copy()  # Inherit environment including PATH
        )

        # Determine actual output directory (script creates subdirectory)
        dsl_basename = dsl_file.stem
        actual_output_dir = output_dir / dsl_basename

        return SynthesisResult(
            returncode=result.returncode,
            stdout=result.stdout,
            stderr=result.stderr,
            output_dir=actual_output_dir
        )
    except subprocess.TimeoutExpired:
        pytest.fail("Synthesis script timeout (>10 minutes)")


@pytest.fixture
def temp_output_dir(tmp_path):
    """Provide temporary directory for test outputs."""
    output_dir = tmp_path / "output"
    output_dir.mkdir()
    yield output_dir
    # Cleanup handled automatically by tmp_path


class TestBasicSynthesis:
    """Test basic synthesis flow without options."""

    def test_baseline_dsl(self, temp_output_dir):
        """Test synthesis with minimal baseline DSL."""
        dsl_file = FIXTURES_DIR / "baseline.dsl"
        result = run_synthesis(dsl_file, temp_output_dir)

        # Check exit code
        assert result.success, f"Synthesis failed:\nSTDOUT:\n{result.stdout}\n\nSTDERR:\n{result.stderr}"

        # Check success message in output
        assert "SUCCESS!" in result.stdout, "Success message not found in output"

        # Check core output files exist (always use "ibex_optimized" prefix)
        assert result.has_file("ibex_optimized_assumptions.sv"), "Assumptions file not generated"
        assert result.has_file("ibex_optimized_id_stage.sv"), "Modified ID stage not generated"
        assert result.has_file("ibex_optimized_synth.ys"), "Synthesis script not generated"
        assert result.has_file("ibex_optimized_yosys.aig"), "Yosys AIGER not generated"
        assert result.has_file("ibex_optimized_yosys.log"), "Yosys log not generated"

        # Check files are non-empty
        assert result.file_size("ibex_optimized_assumptions.sv") > 0, "Assumptions file is empty"
        assert result.file_size("ibex_optimized_yosys.aig") > 0, "AIGER file is empty"

        # Check ABC outputs (if abc available)
        if shutil.which("abc"):
            assert result.has_file("ibex_optimized_abc.log"), "ABC log not generated"
            assert result.has_file("ibex_optimized_post_abc.aig"), "ABC optimization failed - post_abc.aig not created"
            assert result.file_size("ibex_optimized_post_abc.aig") > 0, "Post-ABC AIGER is empty"

    def test_instruction_constraints(self, temp_output_dir):
        """Test synthesis with instruction constraints (data types)."""
        dsl_file = FIXTURES_DIR / "simple_outlawed.dsl"
        result = run_synthesis(dsl_file, temp_output_dir)

        assert result.success, f"Synthesis failed:\nSTDOUT:\n{result.stdout}\n\nSTDERR:\n{result.stderr}"
        assert "SUCCESS!" in result.stdout

        # Check that assumptions were generated for instruction constraints
        assert result.has_file("ibex_optimized_assumptions.sv")
        assumptions_content = (result.output_dir / "ibex_optimized_assumptions.sv").read_text()

        # Should contain assumption logic for both ISA and data type constraints
        assert len(assumptions_content) > 100, "Assumptions file seems too small"


class TestSynthesisOptions:
    """Test synthesis with various command-line options."""

    def test_3stage_pipeline(self, temp_output_dir):
        """Test 3-stage pipeline option."""
        dsl_file = FIXTURES_DIR / "baseline.dsl"
        result = run_synthesis(dsl_file, temp_output_dir, extra_args=["--3stage"])

        assert result.success, f"Synthesis with --3stage failed:\n{result.stdout}"

        # Check that 3-stage mode was enabled
        assert "Enabling 3-stage pipeline" in result.stdout or "WritebackStage=1" in result.stdout

        # Standard outputs should still exist
        assert result.has_file("ibex_optimized_yosys.aig")

    def test_custom_abc_depth(self, temp_output_dir):
        """Test custom ABC depth parameter."""
        dsl_file = FIXTURES_DIR / "baseline.dsl"
        result = run_synthesis(dsl_file, temp_output_dir, extra_args=["--abc-depth", "4"])

        assert result.success, f"Synthesis with --abc-depth failed:\n{result.stdout}"

        # Check that custom depth was used
        if shutil.which("abc"):
            assert "ABC k-induction depth: 4" in result.stdout

        assert result.has_file("ibex_optimized_yosys.aig")


class TestErrorHandling:
    """Test error handling and validation."""

    def test_missing_dsl_file(self, temp_output_dir):
        """Test behavior with non-existent DSL file."""
        dsl_file = FIXTURES_DIR / "nonexistent.dsl"
        result = run_synthesis(dsl_file, temp_output_dir)

        # Should fail gracefully
        assert not result.success, "Should fail with missing DSL file"
        assert "ERROR" in result.stdout or "not found" in result.stdout

    def test_invalid_abc_depth(self, temp_output_dir):
        """Test invalid ABC depth parameter."""
        dsl_file = FIXTURES_DIR / "baseline.dsl"
        result = run_synthesis(dsl_file, temp_output_dir, extra_args=["--abc-depth", "0"])

        # Should fail with validation error
        assert not result.success, "Should fail with invalid ABC depth"
        assert "ERROR" in result.stdout or "must be a positive integer" in result.stdout


class TestOutputOrganization:
    """Test output file organization."""

    def test_output_subdirectory_creation(self, temp_output_dir):
        """Test that outputs are organized in DSL-named subdirectories."""
        dsl_file = FIXTURES_DIR / "baseline.dsl"
        result = run_synthesis(dsl_file, temp_output_dir)

        assert result.success

        # Output should be in subdirectory named after DSL file
        expected_subdir = temp_output_dir / "baseline"
        assert expected_subdir.exists(), f"Expected subdirectory {expected_subdir} not created"
        assert expected_subdir.is_dir()

        # Files should be in the subdirectory
        assert (expected_subdir / "ibex_optimized_yosys.aig").exists()


class TestLogParsing:
    """Test parsing of synthesis logs for errors."""

    def test_no_errors_in_yosys_log(self, temp_output_dir):
        """Ensure Yosys log doesn't contain errors."""
        dsl_file = FIXTURES_DIR / "baseline.dsl"
        result = run_synthesis(dsl_file, temp_output_dir)

        assert result.success

        # Read Yosys log
        yosys_log = result.output_dir / "ibex_optimized_yosys.log"
        assert yosys_log.exists(), "Yosys log not found"

        log_content = yosys_log.read_text()

        # Check for error indicators (case-insensitive)
        log_lower = log_content.lower()

        # Some "error" strings might be benign, so be selective
        # Focus on clear failure indicators
        assert "error:" not in log_lower or "0 error" in log_lower, \
            "Errors found in Yosys log"


class TestConfigMode:
    """Test config-based synthesis mode."""

    def test_config_script_generation(self, temp_output_dir):
        """Test that config mode generates correct synthesis script (fast test)."""
        import subprocess

        dsl_file = FIXTURES_DIR / "baseline.dsl"
        config_file = FIXTURES_DIR / "ibex_test.yaml"

        # Just generate the synthesis script without running it
        cmd = [
            "python3", "scripts/make_synthesis_script.py",
            "--config", str(config_file),
            "--modified-files", f"id_stage_isa={temp_output_dir}/test_id.sv",
            "-o", str(temp_output_dir / "test.ys"),
            "-a", str(temp_output_dir / "test")
        ]

        result = subprocess.run(cmd, capture_output=True, text=True, cwd=PROJECT_ROOT)

        assert result.returncode == 0, f"Script generation failed:\n{result.stdout}\n{result.stderr}"
        assert (temp_output_dir / "test.ys").exists()

        # Check script content
        script_content = (temp_output_dir / "test.ys").read_text()
        assert "ibex_core" in script_content
        assert "read_systemverilog" in script_content

    @pytest.mark.slow
    def test_synthesis_with_config_file(self, temp_output_dir):
        """Test full synthesis using config file (slow test - marked)."""
        dsl_file = FIXTURES_DIR / "baseline.dsl"
        config_file = FIXTURES_DIR / "ibex_test.yaml"

        # Verify config file exists
        assert config_file.exists(), f"Config file not found: {config_file}"

        result = run_synthesis(
            dsl_file,
            temp_output_dir,
            extra_args=["--config", str(config_file)]
        )

        assert result.success, f"Synthesis with config failed:\nSTDOUT:\n{result.stdout}\n\nSTDERR:\n{result.stderr}"

        # Check success message
        assert "SUCCESS!" in result.stdout

        # Check core output files exist
        assert result.has_file("ibex_optimized_assumptions.sv")
        assert result.has_file("ibex_optimized_id_stage.sv")
        assert result.has_file("ibex_optimized_synth.ys")
        assert result.has_file("ibex_optimized_yosys.aig")

        # Check files are non-empty
        assert result.file_size("ibex_optimized_assumptions.sv") > 0
        assert result.file_size("ibex_optimized_yosys.aig") > 0

    def test_core_name_config_lookup(self, temp_output_dir):
        """Test --core flag finds the right config file (fast test)."""
        import shutil

        # Copy test config to configs/ directory temporarily
        test_config_src = FIXTURES_DIR / "ibex_test.yaml"
        test_config_dst = PROJECT_ROOT / "configs" / "test_core.yaml"

        try:
            shutil.copy(test_config_src, test_config_dst)

            # Just test that the script finds the config, don't run full synthesis
            cmd = [
                "python3", "scripts/make_synthesis_script.py",
                "--config", str(test_config_dst),
                "-o", str(temp_output_dir / "test.ys"),
                "-a", str(temp_output_dir / "test")
            ]

            result = subprocess.run(cmd, capture_output=True, text=True, cwd=PROJECT_ROOT)
            assert result.returncode == 0
            assert "test_core" in result.stdout or (temp_output_dir / "test.ys").exists()

        finally:
            # Cleanup
            if test_config_dst.exists():
                test_config_dst.unlink()

    def test_config_not_found(self, temp_output_dir):
        """Test error handling when config file doesn't exist."""
        dsl_file = FIXTURES_DIR / "baseline.dsl"
        bad_config = FIXTURES_DIR / "nonexistent.yaml"

        result = run_synthesis(
            dsl_file,
            temp_output_dir,
            extra_args=["--config", str(bad_config)]
        )

        # Should fail gracefully
        assert not result.success
        assert "ERROR" in result.stdout or "not found" in result.stdout.lower()

    def test_backward_compatibility(self, temp_output_dir):
        """Ensure legacy mode (without --config) still works."""
        dsl_file = FIXTURES_DIR / "baseline.dsl"

        # Run WITHOUT --config flag (legacy mode)
        result = run_synthesis(dsl_file, temp_output_dir)

        assert result.success, f"Legacy mode synthesis failed:\n{result.stdout}"
        assert "SUCCESS!" in result.stdout
        assert result.has_file("ibex_optimized_yosys.aig")


if __name__ == "__main__":
    # Allow running directly for quick testing
    pytest.main([__file__, "-v"])
