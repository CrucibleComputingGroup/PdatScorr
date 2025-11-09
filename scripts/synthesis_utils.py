"""
Shared utilities for synthesis script generation.
"""

from pathlib import Path
from typing import List


def resolve_source_file_path(
    source_file: str,
    core_root: Path,
    pdat_scorr_root: Path = None
) -> str:
    """
    Resolve a source file path, handling special directives.

    Args:
        source_file: Source file path from config (may have @WRAPPER@ prefix)
        core_root: Root directory of the core (e.g., Ibex root)
        pdat_scorr_root: Root of PdatScorr (defaults to this script's parent dir)

    Returns:
        Absolute path to the source file

    Examples:
        >>> resolve_source_file_path("rtl/ibex_core.sv", Path("/ibex"))
        '/ibex/rtl/ibex_core.sv'

        >>> resolve_source_file_path("@WRAPPER@wrapper.sv", Path("/ibex"))
        '/path/to/PdatScorr/wrapper.sv'
    """
    # Special handling for wrapper files marked with @WRAPPER@
    if source_file.startswith("@WRAPPER@"):
        # Remove prefix and resolve relative to PdatScorr directory
        wrapper_file = source_file.replace("@WRAPPER@", "")

        # Default to this script's parent directory if not specified
        if pdat_scorr_root is None:
            pdat_scorr_root = Path(__file__).parent.parent

        wrapper_path = pdat_scorr_root / wrapper_file
        return str(wrapper_path.absolute())

    # Regular file - resolve relative to core root
    source_path = core_root / source_file
    return str(source_path.absolute())


def process_source_files(
    source_files: List[str],
    core_root: Path,
    injection_map: dict = None,
    modified_files: dict = None,
    pdat_scorr_root: Path = None
) -> List[str]:
    """
    Process a list of source files, handling @WRAPPER@ and injection replacements.

    Args:
        source_files: List of source file paths from config
        core_root: Root directory of the core
        injection_map: Dict mapping source file names to injection names
        modified_files: Dict mapping injection names to modified file paths
        pdat_scorr_root: Root of PdatScorr directory

    Returns:
        List of absolute paths to actual source files to use
    """
    injection_map = injection_map or {}
    modified_files = modified_files or {}

    result = []

    for src_file in source_files:
        # Handle @WRAPPER@ directive
        if src_file.startswith("@WRAPPER@"):
            resolved_path = resolve_source_file_path(src_file, core_root, pdat_scorr_root)
            result.append(resolved_path)
            continue

        # Check if this file should be replaced via injection
        if src_file in injection_map:
            inj_name = injection_map[src_file]
            if inj_name in modified_files:
                # Use modified version (ensure it's absolute)
                modified_path = Path(modified_files[inj_name])
                if not modified_path.is_absolute():
                    modified_path = modified_path.absolute()
                result.append(str(modified_path))
            else:
                # Use original (no modification provided for this injection)
                result.append(str((core_root / src_file).absolute()))
        else:
            # Use original file
            result.append(str((core_root / src_file).absolute()))

    return result
