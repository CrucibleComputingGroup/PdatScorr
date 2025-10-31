#!/usr/bin/env python3
"""
Utility functions for regression tests.
"""

from pathlib import Path
from typing import Dict, Optional


def parse_abc_stats(abc_log: Path) -> Optional[Dict[str, int]]:
    """
    Parse ABC log file to extract statistics.

    Args:
        abc_log: Path to ABC log file

    Returns:
        Dictionary with 'inputs', 'outputs', 'latches', 'ands' counts,
        or None if parsing fails
    """
    if not abc_log.exists():
        return None

    try:
        content = abc_log.read_text()

        # Look for lines like: "i/o =    123/   456 lat =   789 and =  12345"
        for line in content.splitlines():
            if "i/o =" in line and "and =" in line:
                parts = line.split()

                # Find indices
                io_idx = parts.index("=", parts.index("i/o"))
                lat_idx = parts.index("=", parts.index("lat"))
                and_idx = parts.index("=", parts.index("and"))

                # Extract values
                inputs = int(parts[io_idx + 1].rstrip("/"))
                outputs = int(parts[io_idx + 2])
                latches = int(parts[lat_idx + 1])
                ands = int(parts[and_idx + 1])

                return {
                    "inputs": inputs,
                    "outputs": outputs,
                    "latches": latches,
                    "ands": ands,
                }
    except (ValueError, IndexError):
        pass

    return None


def check_aiger_valid(aiger_file: Path) -> bool:
    """
    Basic validation of AIGER file format.

    Args:
        aiger_file: Path to AIGER file

    Returns:
        True if file appears to be valid AIGER format
    """
    if not aiger_file.exists() or aiger_file.stat().st_size == 0:
        return False

    try:
        with open(aiger_file, "rb") as f:
            header = f.read(20).decode("ascii", errors="ignore")

            # AIGER files should start with "aig " or "aag "
            return header.startswith("aig ") or header.startswith("aag ")
    except Exception:
        return False


def extract_synthesis_stats(yosys_log: Path) -> Optional[Dict[str, int]]:
    """
    Extract synthesis statistics from Yosys log.

    Args:
        yosys_log: Path to Yosys log file

    Returns:
        Dictionary with synthesis statistics or None if parsing fails
    """
    if not yosys_log.exists():
        return None

    try:
        content = yosys_log.read_text()
        stats = {}

        # Look for chip area (from gate-level synthesis)
        for line in content.splitlines():
            if "Chip area for module" in line:
                # Example: "Chip area for module '\\ibex_core': 123456.789000"
                parts = line.split(":")
                if len(parts) >= 2:
                    area_str = parts[-1].strip()
                    stats["chip_area"] = float(area_str)

        return stats if stats else None
    except Exception:
        return None
