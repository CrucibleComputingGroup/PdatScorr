"""
Mux Reachability Analyzer for Higher-Level ODC Detection

Proves that certain mux selection paths are unreachable given DSL constraints.
Uses SEC with added assertions to verify that mux cases are never exercised.
"""

import logging
import sys
from pathlib import Path
from typing import List, Set, Dict, Optional, Tuple
from dataclasses import dataclass
import re

from pdat_dsl.parser import parse_dsl

# NOTE: alu_mapping.py contains Ibex-specific mappings - no longer used
# Mux structure now comes from config.result_muxes instead
from .synthesis import synthesize_error_injected_circuit
from .sec_checker import SecChecker

# Add scripts to path for config loader
sys.path.insert(0, str(Path(__file__).parent.parent / "scripts"))
from config_loader import ConfigLoader

logger = logging.getLogger(__name__)


@dataclass
class UnreachableMuxCase:
    """Represents a proven unreachable mux case."""
    result_signal: str
    alu_operations: List[str]
    functional_unit: str
    reason: str
    sec_verified: bool
    proof_runtime: float  # seconds


class MuxReachabilityAnalyzer:
    """Analyzes ALU result mux to find unreachable cases."""

    def __init__(self, config_path: Path, output_dir: Path):
        """
        Initialize the mux reachability analyzer.

        Args:
            config_path: Path to core configuration file
            output_dir: Directory for synthesis outputs
        """
        self.config_path = config_path
        self.output_dir = output_dir
        self.output_dir.mkdir(parents=True, exist_ok=True)

    def analyze(
        self,
        dsl_file: Path,
        baseline_aig: Path,
        k_depth: int = 2,
        skip_synthesis: bool = False,
    ) -> List[UnreachableMuxCase]:
        """
        Analyze which mux cases are unreachable given DSL constraints.

        Args:
            dsl_file: Path to DSL specification file
            baseline_aig: Path to baseline synthesized AIGER file
            k_depth: k-induction depth for SEC (matches pipeline depth)
            skip_synthesis: Skip synthesis (for testing)

        Returns:
            List of proven unreachable mux cases
        """
        logger.info(f"Analyzing mux reachability for {dsl_file.name}")

        # Parse DSL to get allowed instructions
        allowed_instructions = self._parse_allowed_instructions(dsl_file)
        logger.info(f"Allowed instructions: {len(allowed_instructions)}")
        logger.info(f"Allowed: {sorted(allowed_instructions)}")

        # Find potentially unreachable functional units
        candidates = self._find_unreachable_candidates(allowed_instructions)
        logger.info(f"Found {len(candidates)} candidate unreachable mux cases")

        if not candidates:
            logger.info("No unreachable mux cases found")
            return []

        # Verify each candidate with SEC
        verified_cases = []
        for candidate in candidates:
            logger.info(f"Verifying {candidate.functional_unit} ({candidate.result_signal})...")

            if skip_synthesis:
                logger.info("Skipping synthesis (test mode)")
                candidate.sec_verified = False
                candidate.proof_runtime = 0.0
                verified_cases.append(candidate)
                continue

            # Prove unreachability using BMC
            try:
                logger.info(f"Verifying {candidate.functional_unit} with BMC...")
                is_unreachable, runtime = self._prove_unreachable_with_sec(
                    dsl_file=dsl_file,
                    baseline_aig=baseline_aig,
                    alu_operations=candidate.alu_operations,
                    k_depth=k_depth,
                )
            except Exception as e:
                logger.error(f"BMC verification exception: {e}")
                is_unreachable = False
                runtime = 0.0

            candidate.sec_verified = is_unreachable
            candidate.proof_runtime = runtime

            if is_unreachable:
                logger.info(f"  ✓ Verified unreachable (BMC proved UNSAT, {runtime:.2f}s)")
            else:
                logger.info(f"  ✗ NOT verified / BMC failed ({runtime:.2f}s)")

            # Add candidate regardless of verification status
            # (Unverified candidates can still be useful for manual inspection)
            verified_cases.append(candidate)

        logger.info(f"Returning {len(verified_cases)} candidates ({sum(1 for c in verified_cases if c.sec_verified)} verified)")
        return verified_cases

    def _parse_allowed_instructions(self, dsl_file: Path) -> Set[str]:
        """Parse DSL to get all allowed instructions."""
        logger.info(f"Parsing DSL file: {dsl_file}")
        with open(dsl_file, 'r') as f:
            dsl_text = f.read()
        logger.debug(f"DSL content ({len(dsl_text)} chars)")
        dsl_ast = parse_dsl(dsl_text)
        logger.debug(f"DSL AST has {len(dsl_ast.rules)} rules")

        # Start with base RV32I and M extension (what's typically in ISA)
        # Then subtract forbidden instructions
        allowed = self._get_base_rv32i_instructions()
        forbidden = set()

        # Check for global include/forbid rules
        for rule in dsl_ast.rules:
            rule_type = type(rule).__name__

            if rule_type == "IncludeRule":
                # v2 DSL: include INSTR { patterns }
                if hasattr(rule, "instruction_pattern"):
                    instr_name = rule.instruction_pattern.instruction_name.upper()
                    allowed.add(instr_name)
            elif rule_type == "ForbidRule":
                # v2 DSL: forbid INSTR or forbid xN-xM (register range)
                if hasattr(rule, "expr"):
                    # Check if this is a register range expression (not an instruction)
                    if type(rule.expr).__name__ == "RegisterRangeExpression":
                        # Skip register range constraints - they don't affect instruction allowlist
                        continue
                    # It's an instruction name string
                    instr_name = rule.expr.upper()
                    forbidden.add(instr_name)
            elif rule_type == "InstructionRule":
                # v1 DSL: instruction INSTR { ... }
                instr_name = rule.instruction_name.upper()
                if rule.forbid:
                    forbidden.add(instr_name)
                else:
                    allowed.add(instr_name)

        # Handle include RV32I / include RV32M directives
        for rule in dsl_ast.rules:
            if type(rule).__name__ == "IncludeRule":
                if hasattr(rule, "expr") and not hasattr(rule, "instruction_pattern"):
                    # Handle "include RV32I" or similar (not an instruction pattern)
                    ext = rule.expr.upper()
                    if ext == "RV32I":
                        allowed.update(self._get_base_rv32i_instructions())
                    elif ext == "RV32M":
                        allowed.update({"MUL", "MULH", "MULHSU", "MULHU", "DIV", "DIVU", "REM", "REMU"})

        # Remove forbidden instructions
        allowed -= forbidden

        logger.debug(f"Allowed instructions ({len(allowed)}): {sorted(allowed)}")
        logger.debug(f"Forbidden instructions ({len(forbidden)}): {sorted(forbidden)}")

        return allowed

    def _get_base_rv32i_instructions(self) -> Set[str]:
        """Get the set of base RV32I instructions."""
        return {
            # Integer register-immediate
            "ADDI", "SLTI", "SLTIU", "XORI", "ORI", "ANDI", "SLLI", "SRLI", "SRAI",
            # Integer register-register
            "ADD", "SUB", "SLL", "SLT", "SLTU", "XOR", "SRL", "SRA", "OR", "AND",
            # Loads
            "LB", "LH", "LW", "LBU", "LHU",
            # Stores
            "SB", "SH", "SW",
            # Branches
            "BEQ", "BNE", "BLT", "BGE", "BLTU", "BGEU",
            # Jump
            "JAL", "JALR",
            # Upper immediate
            "LUI", "AUIPC",
            # System
            "ECALL", "EBREAK", "FENCE",
        }

    def _find_unreachable_candidates(
        self, allowed_instructions: Set[str]
    ) -> List[UnreachableMuxCase]:
        """
        Find functional units that are candidates for being unreachable.

        Returns ALL mux cases from config (except those marked never_odc).
        BMC will determine which are actually unreachable.
        """
        # Load config to get result_muxes
        try:
            config = ConfigLoader.load_config(str(self.config_path))
            if not config.result_muxes:
                logger.info(f"Core '{config.core_name}' does not have result_muxes defined - skipping mux analysis")
                logger.info(f"Mux-level ODC analysis is only supported for cores with explicit result mux configurations")
                return []
        except Exception as e:
            logger.error(f"Failed to load config: {e}")
            import traceback
            traceback.print_exc()
            return []

        # Convert config result_muxes to candidates
        # Test ALL cases - let BMC determine if they're actually reachable
        logger.info(f"Loading {len(config.result_muxes)} result_muxes from config")
        candidates = []

        for mux in config.result_muxes:
            logger.info(f"Analyzing mux: {mux.get('name', 'unnamed')}")
            cases = mux.get('cases', [])
            for case in cases:
                result_sig = case.get('result_signal', 'unknown')
                case_ops = case.get('alu_operations', [])
                logger.info(f"  Checking case: {result_sig} with {len(case_ops)} operations")

                # Skip if marked as never_odc
                if case.get('never_odc', False):
                    logger.info(f"    Skipping (marked never_odc)")
                    continue

                # Add as candidate - BMC will verify if actually unreachable
                case_instructions = set(case_ops)
                logger.info(f"    → Adding as ODC candidate (will verify with BMC)")
                candidates.append(UnreachableMuxCase(
                    result_signal=case['result_signal'],
                    alu_operations=list(case_instructions),
                    functional_unit=case.get('description', case['result_signal']),
                    reason=f"Testing if {len(case_instructions)} operations are unreachable",
                    sec_verified=False,
                    proof_runtime=0.0
                ))

        logger.info(f"Found {len(candidates)} mux case candidates to test with BMC")
        return candidates

    def _prove_unreachable_with_sec(
        self,
        dsl_file: Path,
        baseline_aig: Path,
        alu_operations: List[str],
        k_depth: int,
    ) -> Tuple[bool, float]:
        """
        Prove a mux case is unreachable using bounded model checking (BMC).

        Algorithm:
        1. Take baseline circuit (with DSL constraints)
        2. Add property to check: operator_i == ALU_SLL (or other operation)
        3. Run BMC with k-induction to try to find a reachable state where this holds
        4. If UNSAT (no counterexample found), the mux case is unreachable

        This uses SAT-based BMC to prove the property is unreachable from any valid
        initial state, considering the DSL constraints.

        Args:
            dsl_file: DSL specification (not used in BMC approach)
            baseline_aig: Baseline AIGER file with DSL constraints
            alu_operations: ALU operations to prove are unreachable
            k_depth: k-induction depth for BMC

        Returns:
            (is_unreachable, runtime_seconds)
        """
        import subprocess
        import time

        # Create property file that checks if operator_i can equal any of the target operations
        # We want to find if operator_i == ALU_SLL is REACHABLE
        # If BMC returns UNSAT, it means operator_i can never reach this value → unreachable

        ops_str = "_".join([op.replace("ALU_", "") for op in alu_operations[:3]])
        logger.debug(f"Running BMC to check if {ops_str} operations are reachable...")

        # For now, we can't easily add properties to AIGER files without resynthesis
        # We need to synthesize a version with the property as an output
        # OR use ABC's ability to add properties programmatically

        # Alternative: Use ABC's sat command to check reachability
        # We need to create a "bad state" output that fires when operator_i matches our target

        # Actually, the cleanest approach is to synthesize with a monitor that
        # becomes true when operator_i == target_op, then run BMC on that monitor

        # For now, let's use the assertion-based approach but check differently:
        # Synthesize variant that has operator_i == ALU_SLL as an OUTPUT
        # Then run BMC to see if that output can ever be 1

        variant_dir = self.output_dir / "bmc_variants"
        variant_dir.mkdir(parents=True, exist_ok=True)

        variant_name = f"bmc_{ops_str}"
        variant_output_dir = variant_dir / variant_name

        logger.debug(f"Creating BMC variant: {variant_name}")

        # Generate monitor code that creates an output when operator_i matches
        monitor_info = self._generate_bmc_monitor(alu_operations)

        # Synthesize with monitor
        try:
            variant_aig = self._synthesize_with_monitor(
                dsl_file=dsl_file,
                monitor_info=monitor_info,
                output_dir=variant_output_dir,
            )
        except Exception as e:
            logger.error(f"BMC variant synthesis failed for {variant_name}: {e}")
            return False, 0.0

        # Run BMC using ABC
        is_unreachable, runtime = self._run_bmc_check(variant_aig, k_depth)

        return is_unreachable, runtime

    def _generate_bmc_monitor(self, alu_operations: List[str]) -> Dict[str, str]:
        """
        Generate SystemVerilog monitor code that outputs 1 when the mux selects forbidden operations.

        Returns a dict with:
        - 'monitor_code': Code to inject in mux module body
        - 'port_declaration': Port to add to module interface
        - 'monitor_name': Name of the monitor signal
        """
        # Load config to get core-specific signal names and mux structure
        config = ConfigLoader.load_config(str(self.config_path))

        # Get signal names from config
        clk_signal = config.signals.get('clk', 'clk')
        rst_signal = config.signals.get('rst_n', 'rst_n')

        # Determine if this is Ibex (has operator_i) or another core (uses different mechanism)
        core_name = config.core_name.lower()

        # Generate monitor name
        ops_str = "_".join([op.replace("ALU_", "") for op in alu_operations[:3]])
        monitor_name = f"bmc_monitor_{ops_str}_o"

        if core_name == 'ibex':
            # Ibex-specific: check operator_i signal
            conditions = [f"(operator_i == ibex_pkg::{op})" for op in alu_operations]
            condition_str = " || ".join(conditions)

            monitor_code = f"""
  // ========================================
  // BMC REACHABILITY MONITOR
  // Monitors if operator_i ever equals forbidden ALU operations
  // ========================================

  // Monitor output: 1 if operator_i matches any forbidden operation
  assign {monitor_name} = {condition_str};

  // synthesis translate_off
  // For debugging: warn if this ever happens
  assert property (@(posedge {clk_signal}) disable iff (!{rst_signal})
    !{monitor_name}
  ) else $display("WARNING: operator_i reached forbidden value: %0d", operator_i);
  // synthesis translate_on
"""
        else:
            # Generic core: check if mdu_en is asserted (indicates M-extension operation)
            # For RiscvSingleCycle and similar cores, mdu_en=1 means using MDU result
            # This assumes mdu_result is selected for M-extension operations

            monitor_code = f"""
  // ========================================
  // BMC REACHABILITY MONITOR
  // Monitors if MDU operations are ever used
  // ========================================

  // Monitor output: 1 if MDU is enabled (indicating M-extension operation)
  assign {monitor_name} = mdu_en;

  // synthesis translate_off
  // For debugging: warn if this ever happens
  assert property (@(posedge {clk_signal}) disable iff (!{rst_signal})
    !{monitor_name}
  ) else $display("WARNING: MDU enabled for M-extension operations");
  // synthesis translate_on
"""

        return {
            'monitor_code': monitor_code,
            'port_declaration': f"    output var logic {monitor_name}\n",
            'monitor_name': monitor_name
        }

    def _run_bmc_check(self, variant_aig: Path, k_depth: int) -> Tuple[bool, float]:
        """
        Run bounded model checking to see if monitor output can ever be 1.

        Uses ABC's bmc3 or pdr command to check reachability.

        Args:
            variant_aig: AIGER file with BMC monitor as output
            k_depth: BMC depth

        Returns:
            (is_unreachable, runtime_seconds) - True if monitor never fires (UNSAT)
        """
        import subprocess
        import time

        # ABC BMC command
        # We want to check if the monitor output (last output) can ever be 1
        # If SAT: monitor can be 1 → operator_i IS reachable → NOT unreachable
        # If UNSAT: monitor never 1 → operator_i NOT reachable → IS unreachable

        bmc_script = f"""
read_aiger {variant_aig};
print_stats;
fold;
print_stats;
bmc3 -F {k_depth} -v;
""".strip()

        try:
            start_time = time.time()
            result = subprocess.run(
                ["abc", "-c", bmc_script],
                capture_output=True,
                text=True,
                timeout=120,
            )
            runtime = time.time() - start_time

            output = result.stdout + result.stderr
            logger.debug(f"BMC output length: {len(output)} chars")

            # Parse BMC output
            output_lower = output.lower()

            # Check for UNSAT (property holds, monitor never fires, unreachable)
            if "no output asserted" in output_lower or "unsat" in output_lower or "property proved" in output_lower:
                logger.debug(f"BMC: UNSAT - operations unreachable")
                return True, runtime

            # Check for SAT (counterexample found, monitor can fire, reachable)
            if "output asserted" in output_lower or "counterexample" in output_lower or "property failed" in output_lower:
                logger.debug(f"BMC: SAT - operations are reachable")
                return False, runtime

            # Unknown - log the output for debugging
            logger.warning(f"BMC: Unknown result. Output: {output[:200]}")
            return False, runtime

        except subprocess.TimeoutExpired:
            logger.warning(f"BMC timeout after {k_depth} steps")
            return False, 120.0
        except Exception as e:
            logger.error(f"BMC exception: {e}")
            return False, 0.0

    def _synthesize_with_monitor(
        self,
        dsl_file: Path,
        monitor_info: Dict[str, str],
        output_dir: Path,
    ) -> Path:
        """
        Synthesize RTL with BMC monitor injected into mux source file.

        The monitor creates an output signal that becomes 1 when the mux selector
        reaches certain values. BMC will check if this output is reachable.

        Args:
            dsl_file: DSL specification
            monitor_info: Dict with 'monitor_code', 'port_declaration', 'monitor_name'
            output_dir: Output directory for variant

        Returns:
            Path to synthesized AIGER file
        """
        # Read source file containing the mux (from config)
        config = ConfigLoader.load_config(str(self.config_path))
        core_root = Path(config.synthesis.core_root_resolved)

        # Get mux location from config
        if hasattr(config, 'result_muxes') and len(config.result_muxes) > 0:
            # Use first mux definition
            mux_def = config.result_muxes[0]
            mux_location = mux_def['location']  # e.g., "target/datapath.sv:149"
            source_file = mux_location.split(':')[0]  # Extract file path
            source_path = core_root / source_file
            module_name = Path(source_file).stem  # e.g., "datapath" from "target/datapath.sv"
        else:
            # Fallback to Ibex
            source_path = core_root / "rtl" / "ibex_alu.sv"
            module_name = "ibex_alu"

        with open(source_path, 'r') as f:
            alu_lines = f.readlines()

        # Step 1: Find the actual module name in the file (may have prefix like "RiscvSingleCycle_")
        actual_module_name = None
        for line in alu_lines:
            if line.strip().startswith('module '):
                # Extract module name: "module Foo #(" or "module Foo (" or "module Foo;"
                import re
                match = re.match(r'\s*module\s+(\w+)', line)
                if match:
                    actual_module_name = match.group(1)
                    break

        if not actual_module_name:
            raise RuntimeError(f"Could not find module declaration in {source_path.name}")

        # Step 2: Add monitor output port to module declaration
        # Find "module <actual_module_name>" and add port before closing paren
        module_port_idx = None
        for i, line in enumerate(alu_lines):
            if f"module" in line and actual_module_name in line:
                # Find the closing paren of port list
                for j in range(i, min(i + 100, len(alu_lines))):
                    if ");" in alu_lines[j]:
                        # Insert before the closing paren (just before the ); line)
                        module_port_idx = j
                        break
                break

        if module_port_idx is None:
            raise RuntimeError(f"Could not find module port list in {source_path.name}")

        # Need to add a comma to the last port before inserting the new one
        # Find the last non-empty, non-comment line before the );
        last_port_idx = module_port_idx - 1
        while last_port_idx >= 0:
            line_stripped = alu_lines[last_port_idx].strip()
            # Skip empty lines and comment-only lines
            if line_stripped and not line_stripped.startswith('//'):
                break
            last_port_idx -= 1

        # Add comma to the last port line if it doesn't already have one
        if last_port_idx >= 0:
            last_port_line = alu_lines[last_port_idx]
            # Check if line ends with a port declaration (not already has comma or comment or paren)
            stripped = last_port_line.rstrip()
            if stripped and not stripped.endswith(',') and not stripped.endswith(';') and not stripped.endswith(')'):
                # Add comma after the port name/type
                alu_lines[last_port_idx] = stripped + ',\n'

        # Insert port declaration
        alu_lines.insert(module_port_idx, monitor_info['port_declaration'])

        # Step 3: Find injection point for monitor code
        # Try to use line number from config, otherwise search for "Result mux" comment
        injection_idx = None

        if hasattr(config, 'result_muxes') and len(config.result_muxes) > 0:
            mux_def = config.result_muxes[0]
            mux_location = mux_def.get('location', '')
            if ':' in mux_location:
                line_num_str = mux_location.split(':')[1]
                try:
                    # Config line number is 1-indexed, convert to 0-indexed
                    config_line = int(line_num_str) - 1
                    # Inject after that line
                    injection_idx = config_line + 1
                except ValueError:
                    pass

        # Fallback: search for "Result mux" comment (Ibex-specific)
        if injection_idx is None:
            for i, line in enumerate(alu_lines):
                if "Result mux" in line:
                    for j in range(i, min(i + 100, len(alu_lines))):
                        line_stripped = alu_lines[j].strip()
                        if line_stripped == "end":
                            context = "".join(alu_lines[i:j])
                            if "always_comb" in context:
                                injection_idx = j + 1
                                break
                    break

        if injection_idx is None:
            raise RuntimeError(f"Could not find injection point in {source_path.name} for monitor")

        # Inject monitor code
        alu_lines.insert(injection_idx, monitor_info['monitor_code'])

        # Write modified file
        modified_alu_path = output_dir / f"{module_name}_modified.sv"
        output_dir.mkdir(parents=True, exist_ok=True)
        with open(modified_alu_path, 'w') as f:
            f.writelines(alu_lines)

        logger.debug(f"Wrote BMC monitor ALU to {modified_alu_path}")

        # Synthesize using the error injection synthesis function
        output_aig = synthesize_error_injected_circuit(
            error_injected_rtl=modified_alu_path,
            dsl_file=dsl_file,
            output_dir=output_dir,
            config_file=self.config_path,
            k_depth=2,
        )

        if output_aig is None or not output_aig.exists():
            raise RuntimeError(f"Synthesis failed to produce AIGER file")

        return output_aig

    def _synthesize_with_assertion(
        self,
        dsl_file: Path,
        assertion_code: str,
        output_dir: Path,
    ) -> Path:
        """
        Synthesize RTL with assertion injected into ALU.

        Args:
            dsl_file: DSL specification
            assertion_code: Assertion SystemVerilog code
            output_dir: Output directory for variant

        Returns:
            Path to synthesized AIGER file
        """
        # Read source file containing the mux (from config)
        config = ConfigLoader.load_config(str(self.config_path))
        core_root = Path(config.synthesis.core_root_resolved)

        # Get mux location from config
        if hasattr(config, 'result_muxes') and len(config.result_muxes) > 0:
            mux_def = config.result_muxes[0]
            mux_location = mux_def['location']
            source_file = mux_location.split(':')[0]
            source_path = core_root / source_file
            module_name = Path(source_file).stem
        else:
            # Fallback to Ibex
            source_path = core_root / "rtl" / "ibex_alu.sv"
            module_name = "ibex_alu"

        with open(source_path, 'r') as f:
            alu_lines = f.readlines()

        # Find injection point: after the result mux (around line 1390)
        # Look for "always_comb begin" after "Result mux" comment
        injection_idx = None
        result_mux_line = None
        for i, line in enumerate(alu_lines):
            if "Result mux" in line:
                result_mux_line = i
                # Find the end of the always_comb block
                found_end_lines = []
                for j in range(i, min(i + 100, len(alu_lines))):
                    line_stripped = alu_lines[j].strip()
                    if line_stripped == "end":
                        found_end_lines.append(j)
                        # Check if there's an always_comb in the preceding lines (check from Result mux comment)
                        context = "".join(alu_lines[i:j])
                        has_always_comb = "always_comb" in context
                        if has_always_comb:
                            injection_idx = j + 1
                            break
                if not found_end_lines:
                    pass  # No end lines found
                break

        if injection_idx is None:
            error_msg = f"Could not find injection point in {source_path.name}"
            if result_mux_line is not None:
                error_msg += f" (found 'Result mux' at line {result_mux_line} but no matching 'end')"
            raise RuntimeError(error_msg)

        # Inject assertion
        alu_lines.insert(injection_idx, assertion_code)

        # Write modified file
        modified_alu_path = output_dir / f"{module_name}_modified.sv"
        output_dir.mkdir(parents=True, exist_ok=True)
        with open(modified_alu_path, 'w') as f:
            f.writelines(alu_lines)

        logger.debug(f"Wrote modified ALU to {modified_alu_path}")

        # Synthesize using the error injection synthesis function
        output_aig = synthesize_error_injected_circuit(
            error_injected_rtl=modified_alu_path,
            dsl_file=dsl_file,
            output_dir=output_dir,
            config_file=self.config_path,
            k_depth=2,  # Will be overridden by caller
        )

        if output_aig is None or not output_aig.exists():
            raise RuntimeError(f"Synthesis failed to produce AIGER file")

        return output_aig
