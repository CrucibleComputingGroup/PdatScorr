#!/usr/bin/env python3
"""
Regression tests for DSL v2 syntax and semantics.

Tests ensure that v2 DSL files (with include/forbid) work correctly with synthesis,
and that new features like shamt field and bit patterns function properly.
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
    """Run synthesis script and return results."""
    cmd = [str(SYNTH_SCRIPT)]
    if extra_args:
        cmd.extend(extra_args)
    cmd.extend([str(dsl_file), str(output_dir)])

    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=600,  # 10 minute timeout
            cwd=PROJECT_ROOT,
            env=os.environ.copy()
        )

        # Determine actual output directory
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


class TestDSLv2BasicSyntax:
    """Test basic v2 DSL syntax parsing and code generation."""

    def test_v2_baseline(self, temp_output_dir):
        """Test basic v2 DSL with simple include."""
        dsl_file = FIXTURES_DIR / "v2_baseline.dsl"
        result = run_synthesis(dsl_file, temp_output_dir)

        assert result.success, f"V2 baseline synthesis failed:\nSTDOUT:\n{result.stdout}\n\nSTDERR:\n{result.stderr}"
        assert "DSL version: 2" in result.stdout, "Version 2 not detected"
        assert "Using v2 semantics" in result.stdout, "V2 semantics not used"
        assert "SUCCESS!" in result.stdout

        # Check core outputs
        assert result.has_file("ibex_optimized_assumptions.sv")
        assert result.has_file("ibex_optimized_yosys.aig")

        # Check that v2 positive assertions were generated
        assumptions = (result.output_dir / "ibex_optimized_assumptions.sv").read_text()
        assert "V2: Positive assertion" in assumptions, "V2 positive assertions not generated"
        assert "allow ONLY these patterns" in assumptions, "V2 comment not found"

    def test_v2_forbid(self, temp_output_dir):
        """Test v2 forbid functionality."""
        dsl_file = FIXTURES_DIR / "v2_forbid_mul.dsl"
        result = run_synthesis(dsl_file, temp_output_dir)

        assert result.success, f"V2 forbid synthesis failed:\nSTDOUT:\n{result.stdout}\n\nSTDERR:\n{result.stderr}"
        assert "DSL version: 2" in result.stdout
        assert "forbid: Removed" in result.stdout, "Forbid operations not executed"

        # Check outputs exist
        assert result.has_file("ibex_optimized_assumptions.sv")


class TestDSLv2ShamtField:
    """Test new shamt field for shift instructions."""

    def test_shamt_5bit_pattern(self, temp_output_dir):
        """Test 5-bit shamt field with bit patterns."""
        dsl_file = FIXTURES_DIR / "v2_shamt_restrict.dsl"
        result = run_synthesis(dsl_file, temp_output_dir)

        assert result.success, f"Shamt restriction synthesis failed:\nSTDOUT:\n{result.stdout}\n\nSTDERR:\n{result.stderr}"
        assert "SUCCESS!" in result.stdout

        # Check that shamt patterns were processed
        assumptions = (result.output_dir / "ibex_optimized_assumptions.sv").read_text()
        assert "shamt=5'b" in assumptions, "Shamt field not found in generated code"

        # Check that specific shift amounts are referenced
        assert "SLLI { shamt=" in assumptions
        assert "SRLI { shamt=" in assumptions
        assert "SRAI { shamt=" in assumptions

        # Verify mask includes shamt bits (should be 0xfff0707f for shamt constraints)
        # This mask checks: opcode, funct3, and all 5 shamt bits
        assert "32'hfff0707f" in assumptions, "Shamt mask not correct"


class TestDSLv2BitPatterns:
    """Test bit pattern constraints on immediate fields."""

    def test_bitpattern_imm(self, temp_output_dir):
        """Test 12-bit immediate patterns."""
        dsl_file = FIXTURES_DIR / "v2_bitpattern_imm.dsl"
        result = run_synthesis(dsl_file, temp_output_dir)

        assert result.success, f"Bit pattern synthesis failed:\nSTDOUT:\n{result.stdout}\n\nSTDERR:\n{result.stderr}"

        # Check that bit patterns were processed
        assumptions = (result.output_dir / "ibex_optimized_assumptions.sv").read_text()
        assert "ADDI { imm=12'b" in assumptions, "12-bit immediate patterns not found"

        # Should have exactly 5 ADDI variants
        assert assumptions.count("ADDI { imm=") == 5, "Expected 5 ADDI variants"


class TestDSLv2SequentialSemantics:
    """Test that v2 sequential semantics work correctly."""

    def test_sequential_include_forbid(self, temp_output_dir):
        """Test sequential include/forbid operations."""
        dsl_file = FIXTURES_DIR / "v2_sequential.dsl"
        result = run_synthesis(dsl_file, temp_output_dir)

        assert result.success, f"Sequential synthesis failed:\nSTDOUT:\n{result.stdout}\n\nSTDERR:\n{result.stderr}"

        # Check sequential processing log
        assert "include: Added" in result.stdout
        assert "forbid: Removed" in result.stdout

        # Verify output has constrained patterns
        assumptions = (result.output_dir / "ibex_optimized_assumptions.sv").read_text()
        assert "ADD { rd=" in assumptions, "Constrained ADD not found"
        assert "ADDI { imm=" in assumptions, "Constrained ADDI not found"


class TestDSLv2OutputFormat:
    """Test that v2 generates correct output format."""

    def test_positive_assertions(self, temp_output_dir):
        """Test that v2 generates positive assertions (== not !=)."""
        dsl_file = FIXTURES_DIR / "v2_baseline.dsl"
        result = run_synthesis(dsl_file, temp_output_dir)

        assert result.success
        assumptions = (result.output_dir / "ibex_optimized_assumptions.sv").read_text()

        # V2 should use == for positive assertions, not != for negative
        # Count == vs != in pattern matching
        equals_count = assumptions.count(") == 32'h")
        not_equals_count = assumptions.count(") != 32'h")

        # V2 positive assertions should have more == than !=
        assert equals_count > 0, "No positive assertions found"
        assert equals_count > not_equals_count, "Should use == (positive) more than != (negative) in v2"

    def test_or_combination(self, temp_output_dir):
        """Test that v2 generates OR combination of allowed patterns."""
        dsl_file = FIXTURES_DIR / "v2_bitpattern_imm.dsl"
        result = run_synthesis(dsl_file, temp_output_dir)

        assert result.success
        assumptions = (result.output_dir / "ibex_optimized_assumptions.sv").read_text()

        # Should have OR operators combining patterns
        assert "||" in assumptions, "No OR operators found in v2 output"
        assert "ADDI" in assumptions


class TestDSLv2BackwardCompatibility:
    """Test that v1 DSL files still work."""

    def test_v1_still_works(self, temp_output_dir):
        """Test that v1 DSL (no version directive) still works."""
        dsl_file = FIXTURES_DIR / "baseline.dsl"
        result = run_synthesis(dsl_file, temp_output_dir)

        assert result.success
        assert "DSL version: 1" in result.stdout, "Should default to v1"
        assert "Using v1 semantics" in result.stdout, "Should use v1 semantics"
