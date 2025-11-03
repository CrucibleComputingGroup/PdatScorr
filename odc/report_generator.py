#!/usr/bin/env python3
"""
Report Generator: Create JSON and human-readable reports for ODC analysis

Generates reports showing which bits are observability don't cares based
on SEC results.
"""

import json
from pathlib import Path
from typing import Dict, List
from dataclasses import dataclass, asdict
from datetime import datetime

# Handle both module and standalone imports
try:
    from .constraint_analyzer import ConstantBit
    from .sec_checker import SecResult, SecStatus
except ImportError:
    from constraint_analyzer import ConstantBit
    from sec_checker import SecResult, SecStatus


@dataclass
class OdcTestResult:
    """Result of testing one candidate ODC bit."""
    constant_bit: ConstantBit
    sec_result: SecResult
    
    @property
    def is_odc(self) -> bool:
        """Check if this bit is confirmed as ODC."""
        return self.sec_result.is_equivalent


class ReportGenerator:
    """Generates reports for ODC analysis results."""
    
    def __init__(self, dsl_file: Path, output_dir: Path):
        """
        Initialize report generator.
        
        Args:
            dsl_file: DSL file that was analyzed
            output_dir: Directory for output reports
        """
        self.dsl_file = dsl_file
        self.output_dir = output_dir
        self.output_dir.mkdir(parents=True, exist_ok=True)
    
    def generate_reports(self, test_results: List[OdcTestResult]) -> None:
        """
        Generate both JSON and markdown reports.
        
        Args:
            test_results: List of ODC test results
        """
        # Generate JSON report
        json_file = self.output_dir / "odc_report.json"
        self._generate_json_report(test_results, json_file)
        
        # Generate markdown report
        md_file = self.output_dir / "odc_report.md"
        self._generate_markdown_report(test_results, md_file)
        
        print(f"Reports generated:")
        print(f"  JSON: {json_file}")
        print(f"  Markdown: {md_file}")
    
    def _generate_json_report(self, test_results: List[OdcTestResult], 
                             output_file: Path) -> None:
        """Generate machine-readable JSON report."""
        report = {
            "metadata": {
                "dsl_file": str(self.dsl_file),
                "timestamp": datetime.now().isoformat(),
                "total_tests": len(test_results),
                "confirmed_odcs": sum(1 for r in test_results if r.is_odc)
            },
            "results": []
        }
        
        for result in test_results:
            cb = result.constant_bit
            sec = result.sec_result
            
            report["results"].append({
                "field": cb.field_name,
                "bit_position": cb.bit_position,
                "expected_constant_value": cb.constant_value,
                "instruction": cb.instruction,
                "is_odc": result.is_odc,
                "sec_status": sec.status.value,
                "sec_runtime_sec": sec.runtime_sec,
                "counterexample": sec.counterexample
            })
        
        with open(output_file, 'w') as f:
            json.dump(report, f, indent=2)
    
    def _generate_markdown_report(self, test_results: List[OdcTestResult],
                                  output_file: Path) -> None:
        """Generate human-readable markdown report."""
        # Count ODCs by field
        odc_count = sum(1 for r in test_results if r.is_odc)
        non_odc_count = len(test_results) - odc_count
        
        # Group results by field
        by_field = {}
        for result in test_results:
            field = result.constant_bit.field_name
            if field not in by_field:
                by_field[field] = []
            by_field[field].append(result)
        
        # Generate markdown
        md = []
        md.append(f"# ODC Analysis Report")
        md.append(f"")
        md.append(f"**DSL File:** `{self.dsl_file.name}`  ")
        md.append(f"**Generated:** {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}  ")
        md.append(f"**Total Tests:** {len(test_results)}  ")
        md.append(f"**Confirmed ODCs:** {odc_count}  ")
        md.append(f"**Not ODCs:** {non_odc_count}  ")
        md.append(f"")
        
        md.append(f"## Summary")
        md.append(f"")
        md.append(f"This report shows which signal bits are observability don't cares (ODCs) ")
        md.append(f"based on bounded sequential equivalence checking. An ODC bit can be forced ")
        md.append(f"to a constant without affecting circuit correctness under the given constraints.")
        md.append(f"")
        
        # Results by field
        for field, results in sorted(by_field.items()):
            md.append(f"## Field: `{field}`")
            md.append(f"")
            md.append(f"| Bit | Expected Value | Instruction | ODC? | SEC Status | Runtime (s) |")
            md.append(f"|-----|----------------|-------------|------|------------|-------------|")
            
            for result in sorted(results, key=lambda r: r.constant_bit.bit_position):
                cb = result.constant_bit
                sec = result.sec_result
                
                odc_marker = "✅" if result.is_odc else "❌"
                instr = cb.instruction or "all"
                
                md.append(f"| {cb.bit_position} | {cb.constant_value} | {instr} | "
                         f"{odc_marker} | {sec.status.value} | {sec.runtime_sec:.2f} |")
            
            md.append(f"")
        
        # Detailed results
        md.append(f"## Detailed Results")
        md.append(f"")
        
        for i, result in enumerate(test_results, 1):
            cb = result.constant_bit
            sec = result.sec_result
            
            md.append(f"### Test {i}: {cb.field_name}[{cb.bit_position}]")
            md.append(f"")
            md.append(f"- **Expected constant value:** {cb.constant_value}")
            md.append(f"- **Tested by forcing to:** {cb.constant_value} (testing if this forced constant matters)")
            md.append(f"- **Instruction:** {cb.instruction or 'all'}")
            md.append(f"- **SEC Result:** {sec.status.value.upper()}")
            md.append(f"- **Runtime:** {sec.runtime_sec:.2f} seconds")
            md.append(f"- **Is ODC:** {'YES ✅' if result.is_odc else 'NO ❌'}")
            
            if sec.counterexample:
                md.append(f"- **Counterexample:**")
                md.append(f"  ```")
                md.append(f"  {sec.counterexample}")
                md.append(f"  ```")
            
            md.append(f"")
        
        # Recommendations
        md.append(f"## Recommendations")
        md.append(f"")
        
        confirmed_odcs = [r for r in test_results if r.is_odc]
        if confirmed_odcs:
            md.append(f"The following bits are confirmed ODCs and can be optimized:")
            md.append(f"")
            for result in confirmed_odcs:
                cb = result.constant_bit
                md.append(f"- `{cb.field_name}[{cb.bit_position}]` = {cb.constant_value} "
                         f"in {cb.instruction or 'all instructions'}")
            md.append(f"")
            md.append(f"These bits can be tied to constants in hardware synthesis, ")
            md.append(f"reducing circuit area and power consumption.")
        else:
            md.append(f"No ODCs were confirmed. All tested bits appear to affect circuit behavior.")
        
        md.append(f"")
        
        # Write report
        with open(output_file, 'w') as f:
            f.write('\n'.join(md))


def main():
    """CLI for testing report generator."""
    import argparse
    from constraint_analyzer import ConstantBit
    from sec_checker import SecResult, SecStatus
    
    parser = argparse.ArgumentParser(description="Generate ODC analysis reports")
    parser.add_argument("--dsl", type=Path, required=True, help="DSL file")
    parser.add_argument("--output-dir", type=Path, required=True, help="Output directory")
    
    args = parser.parse_args()
    
    # Create dummy test results for demonstration
    test_results = [
        OdcTestResult(
            constant_bit=ConstantBit("shamt", 4, 0, "SLLI"),
            sec_result=SecResult(SecStatus.EQUIVALENT, 1.23)
        ),
        OdcTestResult(
            constant_bit=ConstantBit("shamt", 3, 0, "SLLI"),
            sec_result=SecResult(SecStatus.EQUIVALENT, 0.98)
        ),
        OdcTestResult(
            constant_bit=ConstantBit("shamt", 2, 0, "SLLI"),
            sec_result=SecResult(SecStatus.NOT_EQUIVALENT, 2.45, "Found counterexample")
        ),
    ]
    
    generator = ReportGenerator(args.dsl, args.output_dir)
    generator.generate_reports(test_results)
    
    return 0


if __name__ == "__main__":
    import sys
    sys.exit(main())
