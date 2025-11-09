"""
ALU Operation Mapping for Ibex Core

Maps RISC-V instructions to Ibex ALU operations and result signals.
Used for higher-level ODC analysis to identify unreachable functional units.
"""

from typing import Dict, List, Set, Optional
from dataclasses import dataclass

# =============================================================================
# Instruction → ALU Operation Mapping
# =============================================================================

INSTRUCTION_TO_ALU_OP: Dict[str, str] = {
    # RV32I Integer Immediate Instructions
    "ADDI": "ALU_ADD",
    "SLTI": "ALU_SLT",
    "SLTIU": "ALU_SLTU",
    "XORI": "ALU_XOR",
    "ORI": "ALU_OR",
    "ANDI": "ALU_AND",
    "SLLI": "ALU_SLL",
    "SRLI": "ALU_SRL",
    "SRAI": "ALU_SRA",

    # RV32I Register-Register Instructions
    "ADD": "ALU_ADD",
    "SUB": "ALU_SUB",
    "SLL": "ALU_SLL",
    "SLT": "ALU_SLT",
    "SLTU": "ALU_SLTU",
    "XOR": "ALU_XOR",
    "SRL": "ALU_SRL",
    "SRA": "ALU_SRA",
    "OR": "ALU_OR",
    "AND": "ALU_AND",

    # RV32B Bit Manipulation (Zba, Zbb, Zbc, Zbs extensions)
    "SH1ADD": "ALU_SH1ADD",
    "SH2ADD": "ALU_SH2ADD",
    "SH3ADD": "ALU_SH3ADD",
    "XNOR": "ALU_XNOR",
    "ORN": "ALU_ORN",
    "ANDN": "ALU_ANDN",
    "ROR": "ALU_ROR",
    "RORI": "ALU_ROR",
    "ROL": "ALU_ROL",
    "SLO": "ALU_SLO",
    "SRO": "ALU_SRO",
    "GREV": "ALU_GREV",
    "GORC": "ALU_GORC",
    "SHFL": "ALU_SHFL",
    "UNSHFL": "ALU_UNSHFL",
    "XPERM.N": "ALU_XPERM_N",
    "XPERM.B": "ALU_XPERM_B",
    "XPERM.H": "ALU_XPERM_H",
    "MIN": "ALU_MIN",
    "MAX": "ALU_MAX",
    "MINU": "ALU_MINU",
    "MAXU": "ALU_MAXU",
    "PACK": "ALU_PACK",
    "PACKH": "ALU_PACKH",
    "PACKU": "ALU_PACKU",
    "SEXT.B": "ALU_SEXTB",
    "SEXT.H": "ALU_SEXTH",
    "CLZ": "ALU_CLZ",
    "CTZ": "ALU_CTZ",
    "CPOP": "ALU_CPOP",
    "CMOV": "ALU_CMOV",
    "CMIX": "ALU_CMIX",
    "FSL": "ALU_FSL",
    "FSR": "ALU_FSR",
    "BSET": "ALU_BSET",
    "BCLR": "ALU_BCLR",
    "BINV": "ALU_BINV",
    "BEXT": "ALU_BEXT",
    "BCOMPRESS": "ALU_BCOMPRESS",
    "BDECOMPRESS": "ALU_BDECOMPRESS",
    "BFP": "ALU_BFP",
    "CLMUL": "ALU_CLMUL",
    "CLMULR": "ALU_CLMULR",
    "CLMULH": "ALU_CLMULH",
    "CRC32.B": "ALU_CRC32_B",
    "CRC32C.B": "ALU_CRC32C_B",
    "CRC32.H": "ALU_CRC32_H",
    "CRC32C.H": "ALU_CRC32C_H",
    "CRC32.W": "ALU_CRC32_W",
    "CRC32C.W": "ALU_CRC32C_W",
}

# Branch instructions use comparison ALU operations
BRANCH_TO_ALU_OP: Dict[str, str] = {
    "BEQ": "ALU_EQ",
    "BNE": "ALU_NE",
    "BLT": "ALU_LT",
    "BGE": "ALU_GE",
    "BLTU": "ALU_LTU",
    "BGEU": "ALU_GEU",
}

# Load/Store use ALU for address calculation
MEMORY_INSTRUCTIONS = {"LB", "LH", "LW", "LBU", "LHU", "SB", "SH", "SW"}
MEMORY_ALU_OP = "ALU_ADD"  # Address = base + offset

# =============================================================================
# ALU Operation → Result Signal Mapping
# =============================================================================

ALU_OP_TO_RESULT_SIGNAL: Dict[str, str] = {
    # Bitwise Logic
    "ALU_XOR": "bwlogic_result",
    "ALU_XNOR": "bwlogic_result",
    "ALU_OR": "bwlogic_result",
    "ALU_ORN": "bwlogic_result",
    "ALU_AND": "bwlogic_result",
    "ALU_ANDN": "bwlogic_result",

    # Adder
    "ALU_ADD": "adder_result",
    "ALU_SUB": "adder_result",
    "ALU_SH1ADD": "adder_result",
    "ALU_SH2ADD": "adder_result",
    "ALU_SH3ADD": "adder_result",

    # Shifter
    "ALU_SLL": "shift_result",
    "ALU_SRL": "shift_result",
    "ALU_SRA": "shift_result",
    "ALU_SLO": "shift_result",
    "ALU_SRO": "shift_result",

    # Shuffle
    "ALU_SHFL": "shuffle_result",
    "ALU_UNSHFL": "shuffle_result",

    # Crossbar Permutation
    "ALU_XPERM_N": "xperm_result",
    "ALU_XPERM_B": "xperm_result",
    "ALU_XPERM_H": "xperm_result",

    # Comparison
    "ALU_EQ": "cmp_result",
    "ALU_NE": "cmp_result",
    "ALU_GE": "cmp_result",
    "ALU_GEU": "cmp_result",
    "ALU_LT": "cmp_result",
    "ALU_LTU": "cmp_result",
    "ALU_SLT": "cmp_result",
    "ALU_SLTU": "cmp_result",

    # MinMax
    "ALU_MIN": "minmax_result",
    "ALU_MAX": "minmax_result",
    "ALU_MINU": "minmax_result",
    "ALU_MAXU": "minmax_result",

    # Bit Counting
    "ALU_CLZ": "bitcnt_result",
    "ALU_CTZ": "bitcnt_result",
    "ALU_CPOP": "bitcnt_result",

    # Pack
    "ALU_PACK": "pack_result",
    "ALU_PACKH": "pack_result",
    "ALU_PACKU": "pack_result",

    # Sign-Extend
    "ALU_SEXTB": "sext_result",
    "ALU_SEXTH": "sext_result",

    # Multicycle Operations
    "ALU_CMIX": "multicycle_result",
    "ALU_CMOV": "multicycle_result",
    "ALU_FSL": "multicycle_result",
    "ALU_FSR": "multicycle_result",
    "ALU_ROL": "multicycle_result",
    "ALU_ROR": "multicycle_result",
    "ALU_CRC32_B": "multicycle_result",
    "ALU_CRC32C_B": "multicycle_result",
    "ALU_CRC32_H": "multicycle_result",
    "ALU_CRC32C_H": "multicycle_result",
    "ALU_CRC32_W": "multicycle_result",
    "ALU_CRC32C_W": "multicycle_result",
    "ALU_BCOMPRESS": "multicycle_result",
    "ALU_BDECOMPRESS": "multicycle_result",

    # Single-Bit Operations
    "ALU_BSET": "singlebit_result",
    "ALU_BCLR": "singlebit_result",
    "ALU_BINV": "singlebit_result",
    "ALU_BEXT": "singlebit_result",

    # Reverse Operations
    "ALU_GREV": "rev_result",
    "ALU_GORC": "rev_result",

    # Bit Field Place
    "ALU_BFP": "bfp_result",

    # Carry-less Multiply
    "ALU_CLMUL": "clmul_result",
    "ALU_CLMULR": "clmul_result",
    "ALU_CLMULH": "clmul_result",
}

# =============================================================================
# Functional Unit Definitions
# =============================================================================

@dataclass
class FunctionalUnit:
    """Represents a functional unit in the ALU."""
    name: str
    result_signal: str
    alu_operations: List[str]
    description: str

    def get_instructions(self) -> Set[str]:
        """Get all instructions that use this functional unit."""
        instructions = set()
        for instr, alu_op in INSTRUCTION_TO_ALU_OP.items():
            if alu_op in self.alu_operations:
                instructions.add(instr)
        # Add branch instructions if comparison unit
        if self.result_signal == "cmp_result":
            for instr, alu_op in BRANCH_TO_ALU_OP.items():
                if alu_op in self.alu_operations:
                    instructions.add(instr)
        return instructions

FUNCTIONAL_UNITS: List[FunctionalUnit] = [
    FunctionalUnit(
        name="shifter",
        result_signal="shift_result",
        alu_operations=["ALU_SLL", "ALU_SRL", "ALU_SRA", "ALU_SLO", "ALU_SRO"],
        description="Barrel shifter for shift operations"
    ),
    FunctionalUnit(
        name="adder",
        result_signal="adder_result",
        alu_operations=["ALU_ADD", "ALU_SUB", "ALU_SH1ADD", "ALU_SH2ADD", "ALU_SH3ADD"],
        description="Adder/subtractor (also used for address calculation)"
    ),
    FunctionalUnit(
        name="bwlogic",
        result_signal="bwlogic_result",
        alu_operations=["ALU_XOR", "ALU_XNOR", "ALU_OR", "ALU_ORN", "ALU_AND", "ALU_ANDN"],
        description="Bitwise logic operations"
    ),
    FunctionalUnit(
        name="comparator",
        result_signal="cmp_result",
        alu_operations=["ALU_EQ", "ALU_NE", "ALU_GE", "ALU_GEU", "ALU_LT", "ALU_LTU", "ALU_SLT", "ALU_SLTU"],
        description="Comparison operations (used by branches and SLT instructions)"
    ),
    FunctionalUnit(
        name="minmax",
        result_signal="minmax_result",
        alu_operations=["ALU_MIN", "ALU_MAX", "ALU_MINU", "ALU_MAXU"],
        description="Min/Max operations (RV32B only)"
    ),
    FunctionalUnit(
        name="bitcnt",
        result_signal="bitcnt_result",
        alu_operations=["ALU_CLZ", "ALU_CTZ", "ALU_CPOP"],
        description="Bit counting operations (RV32B only)"
    ),
    FunctionalUnit(
        name="shuffle",
        result_signal="shuffle_result",
        alu_operations=["ALU_SHFL", "ALU_UNSHFL"],
        description="Shuffle operations (RV32B only)"
    ),
    FunctionalUnit(
        name="xperm",
        result_signal="xperm_result",
        alu_operations=["ALU_XPERM_N", "ALU_XPERM_B", "ALU_XPERM_H"],
        description="Crossbar permutation (RV32B only)"
    ),
]

# =============================================================================
# Helper Functions
# =============================================================================

def get_alu_op_for_instruction(instruction: str) -> Optional[str]:
    """Get the ALU operation for a given instruction."""
    if instruction in INSTRUCTION_TO_ALU_OP:
        return INSTRUCTION_TO_ALU_OP[instruction]
    elif instruction in BRANCH_TO_ALU_OP:
        return BRANCH_TO_ALU_OP[instruction]
    elif instruction in MEMORY_INSTRUCTIONS:
        return MEMORY_ALU_OP
    return None

def get_result_signal_for_alu_op(alu_op: str) -> Optional[str]:
    """Get the result signal for a given ALU operation."""
    return ALU_OP_TO_RESULT_SIGNAL.get(alu_op)

def get_result_signal_for_instruction(instruction: str) -> Optional[str]:
    """Get the result signal for a given instruction."""
    alu_op = get_alu_op_for_instruction(instruction)
    if alu_op:
        return get_result_signal_for_alu_op(alu_op)
    return None

def get_functional_unit_by_result_signal(result_signal: str) -> Optional[FunctionalUnit]:
    """Get the functional unit that produces a given result signal."""
    for unit in FUNCTIONAL_UNITS:
        if unit.result_signal == result_signal:
            return unit
    return None

def is_adder_used_for_memory(instructions: Set[str]) -> bool:
    """Check if the adder is used for memory address calculation."""
    return bool(MEMORY_INSTRUCTIONS & instructions)
