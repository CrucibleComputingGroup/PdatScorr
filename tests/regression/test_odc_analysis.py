#!/usr/bin/env python3
"""
Regression tests for ODC (Observability Don't Care) analysis.

Tests the error injection and bounded SEC workflow for finding
optimization opportunities.
"""

import sys
import pytest
from pathlib import Path

# Add project root to path
PROJECT_ROOT = Path(__file__).parent.parent.parent
sys.path.insert(0, str(PROJECT_ROOT))

from odc.constraint_analyzer import ConstraintAnalyzer, ConstantBit
from odc.error_injector import ErrorInjector
from odc.sec_checker import SecChecker, SecStatus
from odc.report_generator import ReportGenerator, OdcTestResult


FIXTURES_DIR = Path(__file__).parent / "fixtures"
IBEX_RTL_DIR = PROJECT_ROOT.parent / "PdatCoreSim" / "cores" / "ibex" / "rtl"


class TestConstraintAnalyzer:
    """Test DSL constraint analysis for ODC candidates."""

    def test_single_shift_all_bits_constant(self):
        """Test that single shift instruction makes all bits constant."""
        dsl_file = FIXTURES_DIR / "odc_single_shift.dsl"
        analyzer = ConstraintAnalyzer(dsl_file)
        
        constant_bits = analyzer.analyze_field("shamt")
        
        # Should find all 5 shamt bits as constant
        assert len(constant_bits) == 5, f"Expected 5 constant bits, found {len(constant_bits)}"
        
        # Check specific values for shamt=2 (binary: 00010)
        bit_values = {cb.bit_position: cb.constant_value for cb in constant_bits}
        assert bit_values[4] == 0
        assert bit_values[3] == 0
        assert bit_values[2] == 0
        assert bit_values[1] == 1
        assert bit_values[0] == 0

    def test_power_of_2_shifts_partial_constant(self):
        """Test that power-of-2 shifts make only upper bits constant."""
        dsl_file = FIXTURES_DIR / "odc_power_of_2_shifts.dsl"
        analyzer = ConstraintAnalyzer(dsl_file)
        
        constant_bits = analyzer.analyze_field("shamt")
        
        # Should find bit 4 as constant (max value is 8 = 0b01000)
        assert len(constant_bits) >= 1
        
        bit_values = {cb.bit_position: cb.constant_value for cb in constant_bits}
        assert 4 in bit_values
        assert bit_values[4] == 0


class TestErrorInjector:
    """Test error injection into RTL."""

    def test_shift_amount_injection(self, tmp_path):
        """Test that error injection generates valid SystemVerilog."""
        if not IBEX_RTL_DIR.exists():
            pytest.skip("Ibex RTL not found")
        
        injector = ErrorInjector(IBEX_RTL_DIR)
        source_file = IBEX_RTL_DIR / "ibex_alu.sv"
        output_file = tmp_path / "ibex_alu_test.sv"
        
        # Inject error for bit 4 = 0
        success = injector.inject_shift_amount_error(
            source_file, output_file, bit_position=4, forced_value=0
        )
        
        assert success
        assert output_file.exists()
        
        # Check injection code is present
        content = output_file.read_text()
        assert "ODC ERROR INJECTION" in content
        assert "shift_amt[4]" in content
        assert "1'b0" in content

    def test_injection_after_always_comb(self, tmp_path):
        """Test that injection happens after always_comb block."""
        if not IBEX_RTL_DIR.exists():
            pytest.skip("Ibex RTL not found")
        
        injector = ErrorInjector(IBEX_RTL_DIR)
        source_file = IBEX_RTL_DIR / "ibex_alu.sv"
        output_file = tmp_path / "ibex_alu_test.sv"
        
        injector.inject_shift_amount_error(source_file, output_file, 3, 0)
        
        content = output_file.read_text()
        lines = content.split('\n')
        
        # Find the injection
        injection_line = None
        for i, line in enumerate(lines):
            if "ODC ERROR INJECTION" in line:
                injection_line = i
                break
        
        assert injection_line is not None
        
        # Check that "// single-bit mode: shift" comes after injection
        found_comment = False
        for i in range(injection_line, min(injection_line + 10, len(lines))):
            if "// single-bit mode: shift" in lines[i]:
                found_comment = True
                break
        
        assert found_comment, "Injection should be before '// single-bit mode: shift' comment"


class TestOdcReports:
    """Test ODC report generation."""

    def test_report_generation(self, tmp_path):
        """Test that reports are generated correctly."""
        dsl_file = FIXTURES_DIR / "odc_single_shift.dsl"
        
        # Create dummy test results
        from odc.sec_checker import SecResult, SecStatus
        
        test_results = [
            OdcTestResult(
                ConstantBit("shamt", 4, 0, "SLLI"),
                SecResult(SecStatus.EQUIVALENT, 0.05)
            ),
            OdcTestResult(
                ConstantBit("shamt", 3, 0, "SLLI"),
                SecResult(SecStatus.NOT_EQUIVALENT, 0.06, "Output 41 differs")
            ),
        ]
        
        generator = ReportGenerator(dsl_file, tmp_path)
        generator.generate_reports(test_results)
        
        # Check files exist
        assert (tmp_path / "odc_report.json").exists()
        assert (tmp_path / "odc_report.md").exists()
        
        # Check JSON content
        import json
        with open(tmp_path / "odc_report.json") as f:
            report = json.load(f)
        
        assert report["metadata"]["total_tests"] == 2
        assert report["metadata"]["confirmed_odcs"] == 1
        assert len(report["results"]) == 2

    def test_report_markdown_format(self, tmp_path):
        """Test markdown report formatting."""
        dsl_file = FIXTURES_DIR / "odc_single_shift.dsl"
        
        from odc.sec_checker import SecResult, SecStatus
        
        test_results = [
            OdcTestResult(
                ConstantBit("shamt", 4, 0, "SLLI"),
                SecResult(SecStatus.EQUIVALENT, 0.05)
            ),
        ]
        
        generator = ReportGenerator(dsl_file, tmp_path)
        generator.generate_reports(test_results)
        
        md_content = (tmp_path / "odc_report.md").read_text()
        
        # Check key sections exist
        assert "# ODC Analysis Report" in md_content
        assert "## Summary" in md_content
        assert "## Field: `shamt`" in md_content
        assert "## Recommendations" in md_content
        assert "✅" in md_content  # Has checkmark for ODC


class TestOdcIntegration:
    """Integration tests for full ODC workflow (without actual synthesis)."""

    def test_constraint_to_injection_workflow(self, tmp_path):
        """Test workflow from DSL parsing to error injection."""
        if not IBEX_RTL_DIR.exists():
            pytest.skip("Ibex RTL not found")
        
        dsl_file = FIXTURES_DIR / "odc_single_shift.dsl"
        
        # Step 1: Analyze constraints
        analyzer = ConstraintAnalyzer(dsl_file)
        constant_bits = analyzer.analyze_field("shamt")
        
        assert len(constant_bits) == 5
        
        # Step 2: Inject error for first bit
        injector = ErrorInjector(IBEX_RTL_DIR)
        output_file = injector.inject_constant_bit(
            constant_bits[0],
            tmp_path,
            test_opposite=False
        )
        
        assert output_file.exists()
        content = output_file.read_text()
        assert "ODC ERROR INJECTION" in content
