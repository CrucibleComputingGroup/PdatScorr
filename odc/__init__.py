"""
ODC (Observability Don't Care) Analysis Module

This module provides tools for finding optimization opportunities through
error injection and bounded sequential equivalence checking (SEC).

Components:
- constraint_analyzer: Extract constant bits from DSL constraints
- error_injector: Generate RTL with forced constant values
- sec_checker: Run ABC bounded SEC to verify equivalence
- report_generator: Create JSON and human-readable reports
- alu_mapping: Instruction → ALU operation → result signal mappings
- mux_reachability_analyzer: Prove mux cases are unreachable using SEC
"""

__version__ = "0.2.0"

from .constraint_analyzer import ConstraintAnalyzer, ConstantBit
from .error_injector import ErrorInjector
from .sec_checker import SecChecker, SecResult
from .report_generator import ReportGenerator
from .mux_reachability_analyzer import MuxReachabilityAnalyzer, UnreachableMuxCase

__all__ = [
    "ConstraintAnalyzer",
    "ConstantBit",
    "ErrorInjector",
    "SecChecker",
    "SecResult",
    "ReportGenerator",
    "MuxReachabilityAnalyzer",
    "UnreachableMuxCase",
]
