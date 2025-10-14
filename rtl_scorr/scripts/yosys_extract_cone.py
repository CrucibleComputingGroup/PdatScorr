#!/usr/bin/env python3
"""
Extract SMT2 cone using Yosys built-in cone extraction (%ci/%co).

Uses Yosys to:
1. Load the design
2. Select input cone for target signals using %ci
3. Generate SMT2 for only the selected cone

This is much more robust than manual parsing and uses Yosys's native
dependency tracking.
"""

import sys
import subprocess
import tempfile
from pathlib import Path


def extract_cone_with_yosys(rtl_file: Path, module_name: str,
                            target_signals: list, output_smt2: Path,
                            include_dirs: list = None) -> bool:
    """
    Use Yosys to extract cone and generate SMT2.

    Args:
        rtl_file: Input RTL file (already prepared with assumptions)
        module_name: Top module name
        target_signals: List of signal names to extract cones for
        output_smt2: Output SMT2 file path
        include_dirs: List of include directories

    Returns:
        True on success
    """

    # Build include path arguments
    include_args = ""
    if include_dirs:
        for inc_dir in include_dirs:
            include_args += f" -I{inc_dir}"

    # Build Yosys script
    # For Ibex, need to load package and decoder first
    yosys_script = ""
    if 'ibex' in str(rtl_file).lower():
        yosys_script = f"""
# Load Ibex dependencies
read_systemverilog {include_args} -DYOSYS=1 -DSYNTHESIS=1 ./cores/ibex/rtl/ibex_pkg.sv
read_systemverilog {include_args} -DYOSYS=1 -DSYNTHESIS=1 ./cores/ibex/rtl/ibex_decoder.sv
read_systemverilog {include_args} -DYOSYS=1 -DSYNTHESIS=1 ./cores/ibex/rtl/ibex_controller.sv
"""

    yosys_script += f"""
# Load main design
read_systemverilog {include_args} -DYOSYS=1 -DSYNTHESIS=1 {rtl_file}
hierarchy -check -top {module_name}

# Prepare for analysis
proc
async2sync
dffunmap
opt_expr
opt_clean
flatten

# Show all wires before selection
log "All wires in design:"
select -list w:*

# Select input cones for target signals
# Start with empty selection
select -none

"""

    # Add each target signal's input cone
    for signal in target_signals:
        yosys_script += f"""
# Add input cone for {signal}
select -add w:{signal} %ci*

"""

    yosys_script += """
# Show selected cone
log "Selected cone:"
select -list

# Generate SMT2 for only the selected cone
# write_smt2 should respect current selection
write_smt2 -wires """ + str(output_smt2) + """

select -clear
log "✓ Cone SMT2 generated"
"""

    # Write script to temp file
    with tempfile.NamedTemporaryFile(mode='w', suffix='.ys', delete=False) as f:
        f.write(yosys_script)
        script_file = f.name

    try:
        # Run Yosys
        result = subprocess.run(
            ['synlig', '-s', script_file],
            capture_output=True,
            text=True,
            timeout=60
        )

        # Cleanup
        Path(script_file).unlink()

        if result.returncode != 0:
            print("ERROR: Yosys failed")
            print(result.stderr)
            return False

        # Check if output was created
        if not output_smt2.exists():
            print("ERROR: Output SMT2 not created")
            return False

        return True

    except subprocess.TimeoutExpired:
        Path(script_file).unlink()
        print("ERROR: Yosys timeout")
        return False
    except FileNotFoundError:
        Path(script_file).unlink()
        print("ERROR: synlig not found")
        return False


def extract_cone_from_smt2(smt2_file: Path, target_signals: list, output_smt2: Path) -> bool:
    """
    Extract cone from already-generated SMT2 file.

    This is trickier because we'd need to:
    1. Parse SMT2 back into Yosys
    2. Select cones
    3. Re-export

    For now, this loads the original RTL and re-extracts.
    Better approach: Keep the RTLIL around and work from that.
    """
    print("ERROR: Extracting cone from SMT2 not yet implemented")
    print("       Use extract_cone_with_yosys with original RTL instead")
    return False


def main():
    if len(sys.argv) < 4:
        print("Usage: yosys_extract_cone.py <rtl_file> <module_name> <output.smt2> <signal1> [signal2 ...]")
        print("")
        print("Example:")
        print("  yosys_extract_cone.py examples/simple_mux.v simple_mux output/cone.smt2 result data_a")
        print("")
        print("Extracts input cone for specified signals using Yosys %ci command.")
        sys.exit(1)

    rtl_file = Path(sys.argv[1])
    module_name = sys.argv[2]
    output_smt2 = Path(sys.argv[3])
    target_signals = sys.argv[4:]

    if not rtl_file.exists():
        print(f"ERROR: RTL file not found: {rtl_file}")
        sys.exit(1)

    print("=" * 80)
    print("YOSYS CONE EXTRACTION")
    print("=" * 80)
    print(f"RTL:     {rtl_file}")
    print(f"Module:  {module_name}")
    print(f"Targets: {', '.join(target_signals)}")
    print(f"Output:  {output_smt2}")
    print()

    # Determine include directories
    # For Ibex designs
    include_dirs = []
    if 'ibex' in str(rtl_file).lower():
        include_dirs = [
            './cores/ibex/rtl',
            './cores/ibex/shared/rtl',
            './cores/ibex/vendor/lowrisc_ip/ip/prim/rtl',
            './cores/ibex/vendor/lowrisc_ip/dv/sv/dv_utils'
        ]

    success = extract_cone_with_yosys(
        rtl_file, module_name, target_signals, output_smt2, include_dirs
    )

    if success:
        # Print statistics
        original_lines = len(rtl_file.read_text().split('\n'))
        smt2_lines = len(output_smt2.read_text().split('\n'))

        print()
        print(f"✓ Cone extraction successful")
        print(f"  RTL:  {original_lines} lines")
        print(f"  SMT2: {smt2_lines} lines")
    else:
        print()
        print("✗ Cone extraction failed")
        sys.exit(1)


if __name__ == '__main__':
    main()
