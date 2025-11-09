#!/usr/bin/env python3
"""
Apply Mux-Level ODC Optimizations

Removes unreachable mux cases from RTL based on proven higher-level ODCs.
"""

import argparse
import json
import logging
import re
import sys
from pathlib import Path
from typing import List, Set, Dict

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))
sys.path.insert(0, str(Path(__file__).parent))  # For config_loader

from config_loader import ConfigLoader

logging.basicConfig(
    level=logging.INFO,
    format='%(levelname)s: %(message)s'
)
logger = logging.getLogger(__name__)


def load_unreachable_mux_cases(report_json: Path) -> List[Dict]:
    """Load unreachable mux cases from ODC analysis report."""
    with open(report_json, 'r') as f:
        report = json.load(f)

    if "unreachable_mux_cases" not in report:
        logger.warning("No unreachable_mux_cases found in report")
        return []

    return report["unreachable_mux_cases"]


def remove_mux_cases_from_alu(
    alu_path: Path,
    unreachable_cases: List[Dict],
    output_path: Path,
) -> bool:
    """
    Remove unreachable mux cases from ibex_alu.sv result mux.

    Args:
        alu_path: Path to original ibex_alu.sv
        unreachable_cases: List of unreachable mux case dicts
        output_path: Path to write optimized ALU

    Returns:
        True if any optimizations were applied
    """
    with open(alu_path, 'r') as f:
        lines = f.readlines()

    # Extract ALU operations to remove
    ops_to_remove = set()
    for case in unreachable_cases:
        if case.get("sec_verified", False):
            ops_to_remove.update(case["alu_operations"])

    if not ops_to_remove:
        logger.info("No verified unreachable cases to remove")
        return False

    logger.info(f"Removing {len(ops_to_remove)} ALU operations from result mux:")
    for op in sorted(ops_to_remove):
        logger.info(f"  - {op}")

    # Find the result mux (around line 1322)
    mux_start_idx = None
    mux_end_idx = None

    for i, line in enumerate(lines):
        if "Result mux" in line:
            # Find the always_comb block
            for j in range(i, min(i + 10, len(lines))):
                if "always_comb begin" in lines[j]:
                    mux_start_idx = j
                    break

            # Find the end of the case statement
            if mux_start_idx:
                for j in range(mux_start_idx, min(mux_start_idx + 200, len(lines))):
                    if lines[j].strip() == "endcase":
                        mux_end_idx = j
                        break
            break

    if mux_start_idx is None or mux_end_idx is None:
        raise RuntimeError("Could not find result mux in ibex_alu.sv")

    logger.debug(f"Found result mux at lines {mux_start_idx}-{mux_end_idx}")

    # Parse and modify the case statement
    modified_lines = lines[:mux_start_idx]
    removed_count = 0

    i = mux_start_idx
    while i <= mux_end_idx:
        line = lines[i]

        # Check if this line contains any of the operations to remove
        contains_removed_op = any(op in line for op in ops_to_remove)

        if contains_removed_op:
            # This is a case we want to remove
            # Collect the full case (may span multiple lines)
            case_lines = [line]
            j = i + 1

            # Keep collecting until we hit the result assignment
            while j <= mux_end_idx:
                case_lines.append(lines[j])
                if "result_o =" in lines[j]:
                    j += 1
                    break
                j += 1

            # Add comment explaining removal
            ops_in_case = [op for op in ops_to_remove if any(op in l for l in case_lines)]
            comment = f"  // ODC: Removed unreachable case - operations never occur: {', '.join(ops_in_case)}\n"
            modified_lines.append(comment)

            removed_count += 1
            i = j
        else:
            # Keep this line
            modified_lines.append(line)
            i += 1

    # Add remaining lines after mux
    modified_lines.extend(lines[mux_end_idx + 1:])

    logger.info(f"Removed {removed_count} mux cases")

    # Write optimized file
    with open(output_path, 'w') as f:
        f.writelines(modified_lines)

    logger.info(f"Wrote optimized ALU to {output_path}")
    return True


def comment_out_unused_functional_unit(
    alu_path: Path,
    functional_unit: str,
    output_path: Path,
) -> bool:
    """
    Comment out the logic for an unused functional unit.

    Args:
        alu_path: Path to ALU file (may be already partially optimized)
        functional_unit: Name of functional unit to comment out
        output_path: Path to write optimized ALU

    Returns:
        True if unit was found and commented out
    """
    # Map functional unit names to signal patterns
    unit_signals = {
        "shifter": {
            "result_signal": "shift_result",
            "start_patterns": ["// Shift operations", "shifter_result", "shift_operand"],
            "end_pattern": "assign shift_result",
        },
        "bwlogic": {
            "result_signal": "bwlogic_result",
            "start_patterns": ["// Bitwise Logic Operations"],
            "end_pattern": "assign bwlogic_result",
        },
    }

    if functional_unit not in unit_signals:
        logger.warning(f"Don't know how to comment out functional unit: {functional_unit}")
        return False

    with open(alu_path, 'r') as f:
        lines = f.readlines()

    # For now, just tie the result signal to 0
    # (More aggressive optimization would comment out the entire logic block)
    unit_info = unit_signals[functional_unit]
    result_signal = unit_info["result_signal"]

    modified = False
    for i, line in enumerate(lines):
        if f"assign {result_signal}" in line and "ODC" not in line:
            # Replace the assignment with a tie-off
            indent = len(line) - len(line.lstrip())
            comment = " " * indent + f"// ODC: {functional_unit} is unreachable - tie result to 0\n"
            tie_off = " " * indent + f"assign {result_signal} = 32'b0;\n"
            lines[i] = comment + tie_off
            modified = True
            logger.info(f"Tied {result_signal} to 0 (unreachable {functional_unit})")
            break

    if not modified:
        logger.warning(f"Could not find assignment for {result_signal}")
        return False

    with open(output_path, 'w') as f:
        f.writelines(lines)

    return True


def main():
    parser = argparse.ArgumentParser(
        description="Apply mux-level ODC optimizations by removing unreachable cases"
    )
    parser.add_argument(
        "report_json",
        type=Path,
        help="Path to ODC analysis report JSON"
    )
    parser.add_argument(
        "--config",
        type=Path,
        default=Path(__file__).parent.parent / "configs" / "ibex.yaml",
        help="Core configuration file"
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        required=True,
        help="Output directory for optimized RTL"
    )
    parser.add_argument(
        "--comment-out-units",
        action="store_true",
        help="Also comment out unused functional unit logic (more aggressive)"
    )

    args = parser.parse_args()

    # Load configuration
    config = ConfigLoader.load_config(str(args.config))
    core_root = Path(config.synthesis.core_root_resolved)
    alu_path = core_root / "rtl" / "ibex_alu.sv"

    if not alu_path.exists():
        logger.error(f"ALU file not found: {alu_path}")
        return 1

    # Load unreachable mux cases
    unreachable_cases = load_unreachable_mux_cases(args.report_json)
    if not unreachable_cases:
        logger.info("No unreachable mux cases to optimize")
        return 0

    # Create output directory
    args.output_dir.mkdir(parents=True, exist_ok=True)

    # Step 1: Remove unreachable mux cases
    optimized_alu_path = args.output_dir / "ibex_alu_mux_optimized.sv"
    modified = remove_mux_cases_from_alu(alu_path, unreachable_cases, optimized_alu_path)

    if not modified:
        logger.info("No mux optimizations applied")
        return 0

    # Step 2: Optionally comment out unused functional units
    if args.comment_out_units:
        for case in unreachable_cases:
            if case.get("sec_verified", False):
                unit_name = case["functional_unit"]
                logger.info(f"Commenting out unused unit: {unit_name}")
                temp_path = args.output_dir / f"ibex_alu_temp.sv"
                comment_out_unused_functional_unit(
                    optimized_alu_path,
                    unit_name,
                    temp_path,
                )
                # Move temp to optimized
                temp_path.replace(optimized_alu_path)

    logger.info(f"\nOptimized ALU written to: {optimized_alu_path}")
    logger.info("To use this optimized ALU, pass it to synthesis with --alu-modified flag")

    return 0


if __name__ == "__main__":
    sys.exit(main())
