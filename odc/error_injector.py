#!/usr/bin/env python3
"""
Error Injector: Generate RTL with forced constant values

Creates modified RTL where specific signal bits are forced to constant values.
This is used to test if these forced constants affect circuit behavior (ODC analysis).
"""

import re
import sys
from pathlib import Path
from typing import Dict, List, Optional
from dataclasses import dataclass

# Handle both module and standalone imports
try:
    from .constraint_analyzer import ConstantBit
except ImportError:
    from constraint_analyzer import ConstantBit


@dataclass
class InjectionConfig:
    """Configuration for error injection."""
    source_file: Path
    output_file: Path
    field_name: str
    bit_position: int
    forced_value: int  # 0 or 1
    signal_name: str = "shift_amt"  # Default to shift amount
    signal_width: int = 5  # Default 5-bit shift amount


class ErrorInjector:
    """Generates RTL with forced constant values for ODC testing."""

    def __init__(self, core_rtl_dir: Path, config=None):
        """
        Initialize error injector.

        Args:
            core_rtl_dir: Path to core RTL directory (e.g., ibex/rtl/)
            config: CoreConfig object (optional, for core-agnostic operation)
        """
        self.core_rtl_dir = core_rtl_dir
        self.config = config
    
    def inject_shift_amount_error(self, source_file: Path, output_file: Path,
                                  bit_position: int, forced_value: int) -> bool:
        """
        Inject error forcing for shift amount bit.

        Modifies the shift_amt assignment to force a specific bit to constant.

        Args:
            source_file: Original ibex_alu.sv file
            output_file: Modified output file
            bit_position: Which bit to force (0-4 for 5-bit shamt)
            forced_value: Value to force (0 or 1)

        Returns:
            True if successful
        """
        with open(source_file, 'r') as f:
            content = f.read()

        # Strategy: Find the comment "// single-bit mode: shift" which comes
        # right after the shift_amt assignment block (line ~292)
        # Inject right before this comment
        lines = content.split('\n')
        injection_line = None

        for i, line in enumerate(lines):
            if '// single-bit mode: shift' in line:
                injection_line = i
                break

        if injection_line is None:
            raise ValueError("Could not find injection point in ibex_alu.sv (looking for '// single-bit mode: shift' comment)")

        # Generate simple override code
        injection_code = f"""
  // ========================================
  // ODC ERROR INJECTION: Force shift_amt[{bit_position}] = {forced_value}
  // ========================================
  // Override shift_amt[{bit_position}] after the always_comb block
  assign shift_amt[{bit_position}] = 1'b{forced_value};
"""

        # Inject after the "end"
        lines.insert(injection_line, injection_code)
        modified_content = '\n'.join(lines)

        # Write modified content
        output_file.parent.mkdir(parents=True, exist_ok=True)
        with open(output_file, 'w') as f:
            f.write(modified_content)

        return True

    def inject_register_field_error(self, source_file: Path, output_file: Path,
                                     field_name: str, bit_position: int, forced_value: int) -> bool:
        """
        Inject error forcing for register address field bit.

        For Ibex, modifies ibex_id_stage.sv to force rd/rs1/rs2 address bits.

        Args:
            source_file: Original ibex_id_stage.sv file
            output_file: Modified output file
            field_name: Which field ("rd", "rs1", "rs2")
            bit_position: Which bit to force (0-4 for 5-bit address)
            forced_value: Value to force (0 or 1)

        Returns:
            True if successful
        """
        with open(source_file, 'r') as f:
            content = f.read()

        # Find where register fields are used in ID stage
        # In Ibex, these are typically extracted from instr_rdata_i
        # We'll inject right after the assumptions block (where our constraints are)

        lines = content.split('\n')
        injection_line = None

        # Look for the end of the assumptions block
        for i, line in enumerate(lines):
            if 'Auto-generated instruction constraints' in line:
                # Find the end of this block
                for j in range(i, min(i + 100, len(lines))):
                    if lines[j].strip() == 'end':
                        injection_line = j + 1
                        break
                break

        if injection_line is None:
            # Fallback: inject before endmodule
            for i in range(len(lines) - 1, -1, -1):
                if 'endmodule' in lines[i]:
                    injection_line = i
                    break

        if injection_line is None:
            raise ValueError(f"Could not find injection point in {source_file.name}")

        # Map field names to instruction bit ranges
        field_ranges = {
            "rd": "[11:7]",
            "rs1": "[19:15]",
            "rs2": "[24:20]"
        }

        bit_range = field_ranges.get(field_name)
        if not bit_range:
            raise ValueError(f"Unknown register field: {field_name}")

        # Calculate absolute bit position in instruction
        base_positions = {"rd": 7, "rs1": 15, "rs2": 20}
        absolute_bit = base_positions[field_name] + bit_position

        # Generate injection code
        injection_code = f"""
  // ========================================
  // ODC ERROR INJECTION: Force {field_name}[{bit_position}] = {forced_value}
  // ========================================
  // Override {field_name} address bit after instruction decode
  assign instr_rdata_i[{absolute_bit}] = 1'b{forced_value};
"""

        lines.insert(injection_line, injection_code)
        modified_content = '\n'.join(lines)

        # Write modified content
        output_file.parent.mkdir(parents=True, exist_ok=True)
        with open(output_file, 'w') as f:
            f.write(modified_content)

        return True

    def inject_immediate_error(self, source_file: Path, output_file: Path,
                               bit_position: int, forced_value: int) -> bool:
        """
        Inject error forcing for immediate field bit.
        
        This would be injected in the ID stage where immediates are decoded.
        
        Args:
            source_file: Original ibex_id_stage.sv file
            output_file: Modified output file
            bit_position: Which bit to force (0-11 for 12-bit imm)
            forced_value: Value to force (0 or 1)
            
        Returns:
            True if successful
        """
        # TODO: Implement for immediate fields
        # This is more complex as immediates are decoded in ID stage
        raise NotImplementedError("Immediate error injection not yet implemented")
    
    def inject_constant_bit(self, constant_bit: ConstantBit,
                           output_dir: Path,
                           test_opposite: bool = False) -> Path:
        """
        Inject error for a ConstantBit candidate.

        Args:
            constant_bit: ConstantBit to test
            output_dir: Directory for output files
            test_opposite: If False (default), force bit to constraint-specified constant
                          If True, force to opposite (for negative testing)

        Returns:
            Path to generated error-injected file
        """
        # Determine which file to modify based on field and config
        forced_value = constant_bit.constant_value if not test_opposite else 1 - constant_bit.constant_value

        if constant_bit.field_name == "shamt":
            # Use ALU/ODC error injection point from config if available
            if self.config:
                odc_inj = self.config.get_injection("odc_error")
                if odc_inj:
                    source_file = Path(self.config.synthesis.core_root_resolved) / odc_inj.source_file
                    source_basename = Path(odc_inj.source_file).stem
                else:
                    # Fallback for Ibex
                    source_file = self.core_rtl_dir / "ibex_alu.sv"
                    source_basename = "ibex_alu"
            else:
                # Legacy mode
                source_file = self.core_rtl_dir / "ibex_alu.sv"
                source_basename = "ibex_alu"

            output_filename = (
                f"{source_basename}_odc_{constant_bit.field_name}_bit{constant_bit.bit_position}_forced{forced_value}.sv"
            )
        elif constant_bit.field_name in ["imm", "rd", "rs1", "rs2"]:
            # Use ISA injection point from config if available
            if self.config:
                isa_inj = self.config.get_injection("isa")
                if isa_inj:
                    source_file = Path(self.config.synthesis.core_root_resolved) / isa_inj.source_file
                    source_basename = Path(isa_inj.source_file).stem
                else:
                    # Fallback for Ibex
                    source_file = self.core_rtl_dir / "ibex_id_stage.sv"
                    source_basename = "ibex_id_stage"
            else:
                # Legacy mode
                source_file = self.core_rtl_dir / "ibex_id_stage.sv"
                source_basename = "ibex_id_stage"

            output_filename = (
                f"{source_basename}_odc_{constant_bit.field_name}_bit{constant_bit.bit_position}_forced{forced_value}.sv"
            )
        else:
            raise ValueError(f"Unsupported field for error injection: {constant_bit.field_name}")

        output_file = output_dir / output_filename

        # Force bit to the constraint-specified constant value for ODC testing
        # This tests: "Does forcing the bit to the 'correct' value affect behavior?"
        # If baseline (potentially wrong) ≡ forced (correct) → bit is ODC
        forced_value = constant_bit.constant_value if not test_opposite else (1 - constant_bit.constant_value)
        
        if constant_bit.field_name == "shamt":
            self.inject_shift_amount_error(source_file, output_file,
                                          constant_bit.bit_position, forced_value)
        elif constant_bit.field_name == "imm":
            self.inject_immediate_error(source_file, output_file,
                                       constant_bit.bit_position, forced_value)
        elif constant_bit.field_name in ["rd", "rs1", "rs2"]:
            self.inject_register_field_error(source_file, output_file,
                                            constant_bit.field_name,
                                            constant_bit.bit_position, forced_value)
        else:
            raise ValueError(f"Unsupported field for error injection: {constant_bit.field_name}")

        return output_file


def main():
    """CLI interface for testing error injector."""
    import argparse
    
    parser = argparse.ArgumentParser(description="Inject ODC errors into RTL")
    parser.add_argument("--core-rtl", type=Path, required=True,
                       help="Path to core RTL directory")
    parser.add_argument("--source", type=Path, required=True,
                       help="Source RTL file")
    parser.add_argument("--output", type=Path, required=True,
                       help="Output RTL file")
    parser.add_argument("--field", choices=["shamt", "imm"], default="shamt",
                       help="Field to inject error into")
    parser.add_argument("--bit", type=int, required=True,
                       help="Bit position to force")
    parser.add_argument("--value", type=int, choices=[0, 1], required=True,
                       help="Value to force (0 or 1)")
    
    args = parser.parse_args()
    
    injector = ErrorInjector(args.core_rtl)
    
    if args.field == "shamt":
        success = injector.inject_shift_amount_error(
            args.source, args.output, args.bit, args.value
        )
    else:
        print("ERROR: Only shamt injection implemented currently")
        return 1
    
    if success:
        print(f"Successfully generated error-injected RTL: {args.output}")
        print(f"  Field: {args.field}[{args.bit}]")
        print(f"  Forced value: {args.value}")
        return 0
    else:
        print("ERROR: Injection failed")
        return 1


if __name__ == "__main__":
    sys.exit(main())
