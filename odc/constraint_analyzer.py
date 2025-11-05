#!/usr/bin/env python3
"""
Constraint Analyzer: Extract constant bits from DSL constraints

Analyzes DSL files with bit pattern constraints to identify which bits
should be constant across all allowed patterns. These constant bits are
candidates for ODC analysis.
"""

import sys
from pathlib import Path
from dataclasses import dataclass
from typing import Dict, List, Optional
from collections import defaultdict

# Add parent directory to path to import pdat_dsl
sys.path.insert(0, str(Path(__file__).parent.parent.parent / "PdatRiscvDsl"))

from pdat_dsl.parser import parse_dsl, BitPattern, FieldConstraint, IncludeRule, ForbidRule, InstructionPattern
from pdat_dsl.encodings import get_instruction_encoding


@dataclass
class ConstantBit:
    """Represents a bit that should be constant based on constraints."""
    field_name: str
    bit_position: int  # Position within the field (0-indexed)
    constant_value: int  # 0 or 1
    instruction: Optional[str] = None  # Instruction this applies to (if specific)
    
    def __str__(self):
        instr_str = f" in {self.instruction}" if self.instruction else ""
        return f"{self.field_name}[{self.bit_position}] = {self.constant_value}{instr_str}"


class ConstraintAnalyzer:
    """Analyzes DSL constraints to find constant bits."""
    
    def __init__(self, dsl_file: Path):
        """
        Initialize analyzer with DSL file.
        
        Args:
            dsl_file: Path to DSL file
        """
        self.dsl_file = dsl_file
        with open(dsl_file, 'r') as f:
            dsl_text = f.read()
        self.dsl_spec = parse_dsl(dsl_text)
        
    def analyze_field(self, field_name: str) -> List[ConstantBit]:
        """
        Analyze a specific field to find constant bits.
        
        Args:
            field_name: Name of field to analyze (e.g., "shamt", "imm")
            
        Returns:
            List of ConstantBit objects for bits that are constant
        """
        constant_bits = []
        
        # Group patterns by instruction
        patterns_by_instr = defaultdict(list)
        
        for rule in self.dsl_spec.rules:
            # Handle v2 DSL (IncludeRule with InstructionPattern)
            if isinstance(rule, IncludeRule) and isinstance(rule.expr, InstructionPattern):
                instr_pattern = rule.expr
                for constraint in instr_pattern.constraints:
                    if constraint.field_name == field_name:
                        if isinstance(constraint.field_value, BitPattern):
                            patterns_by_instr[instr_pattern.name].append(
                                constraint.field_value
                            )
            # Handle v1 DSL (InstructionRule)
            elif hasattr(rule, 'name') and hasattr(rule, 'constraints'):
                for constraint in rule.constraints:
                    if constraint.field_name == field_name:
                        if isinstance(constraint.field_value, BitPattern):
                            patterns_by_instr[rule.name].append(
                                constraint.field_value
                            )
        
        # Analyze each instruction's patterns
        for instr_name, patterns in patterns_by_instr.items():
            if not patterns:
                continue
                
            # Get field width from instruction encoding
            try:
                encoding = get_instruction_encoding(instr_name)
                if field_name not in encoding.fields:
                    continue
                field_pos, field_width = encoding.fields[field_name]
            except Exception:
                # Default widths for common fields
                field_width = {
                    "shamt": 5,
                    "imm": 12,
                    "rd": 5,
                    "rs1": 5,
                    "rs2": 5,
                }.get(field_name, 32)
            
            # Find bits that are constant across all patterns
            const_bits = self._find_constant_bits(patterns, field_width)
            
            for bit_pos, value in const_bits.items():
                constant_bits.append(ConstantBit(
                    field_name=field_name,
                    bit_position=bit_pos,
                    constant_value=value,
                    instruction=instr_name
                ))
        
        return constant_bits
    
    def _find_constant_bits(self, patterns: List[BitPattern], 
                           field_width: int) -> Dict[int, int]:
        """
        Find bits that have the same value across all patterns.
        
        Args:
            patterns: List of BitPattern objects
            field_width: Width of the field in bits
            
        Returns:
            Dictionary mapping bit position to constant value
        """
        if not patterns:
            return {}
        
        constant_bits = {}
        
        for bit_pos in range(field_width):
            # Collect values for this bit across all patterns
            bit_values = set()
            all_constrained = True
            
            for pattern in patterns:
                pattern_val, mask_val = pattern.to_pattern_mask()
                
                # Check if this bit is constrained in this pattern
                if mask_val & (1 << bit_pos):
                    bit_value = (pattern_val >> bit_pos) & 1
                    bit_values.add(bit_value)
                else:
                    # This bit is "don't care" in this pattern
                    all_constrained = False
                    break
            
            # If all patterns constrain this bit to the same value, it's constant
            if all_constrained and len(bit_values) == 1:
                constant_bits[bit_pos] = bit_values.pop()
        
        return constant_bits
    
    def analyze_all_fields(self, scope: str = "shamt") -> List[ConstantBit]:
        """
        Analyze all relevant fields based on scope.
        
        Args:
            scope: "shamt" for shift amount only, "all" for all fields
            
        Returns:
            List of all constant bits found
        """
        if scope == "shamt":
            fields = ["shamt"]
        else:
            fields = ["shamt", "imm", "rd", "rs1", "rs2"]
        
        all_constant_bits = []
        for field in fields:
            constant_bits = self.analyze_field(field)
            all_constant_bits.extend(constant_bits)
        
        return all_constant_bits
    
    def get_candidate_odc_bits(self, scope: str = "shamt") -> List[ConstantBit]:
        """
        Get candidate ODC bits for error injection testing.
        
        These are bits that should be constant according to constraints,
        so forcing them to a different value tests if they're true ODCs.
        
        Args:
            scope: "shamt" for shift amount only, "all" for all fields
            
        Returns:
            List of ConstantBit objects representing ODC candidates
        """
        return self.analyze_all_fields(scope)


def main():
    """CLI interface for testing constraint analyzer."""
    import argparse
    
    parser = argparse.ArgumentParser(description="Analyze DSL constraints for constant bits")
    parser.add_argument("dsl_file", type=Path, help="DSL file to analyze")
    parser.add_argument("--field", default="shamt", help="Field to analyze (default: shamt)")
    parser.add_argument("--scope", choices=["shamt", "all"], default="shamt",
                       help="Analysis scope")
    
    args = parser.parse_args()
    
    if not args.dsl_file.exists():
        print(f"ERROR: DSL file not found: {args.dsl_file}")
        return 1
    
    analyzer = ConstraintAnalyzer(args.dsl_file)
    
    if args.field:
        constant_bits = analyzer.analyze_field(args.field)
        print(f"\nConstant bits in field '{args.field}':")
    else:
        constant_bits = analyzer.analyze_all_fields(args.scope)
        print(f"\nAll constant bits (scope={args.scope}):")
    
    if not constant_bits:
        print("  None found")
    else:
        for cb in constant_bits:
            print(f"  {cb}")
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
