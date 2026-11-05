"""Generic scalar-control constants, with no queue-index or capacity knowledge.

Only a selected unique combinational driver is replaced. Its output wire, every
port/net name, all other cells, and every input/state driver remain unchanged.
These are untrusted candidates: only a separate two-design proof can accept one.
"""
from __future__ import annotations

from collections import Counter
import copy
import re

from .temporal import validate_hardware


SCALAR_TYPES = frozenset({"$eq", "$logic_not"})


def _eligible_outputs(design: dict, top: str) -> dict[str, int]:
    validate_hardware(design, top)
    module = design["modules"][top]
    inputs = {bit for port in module.get("ports", {}).values()
              if port["direction"] in {"input", "inout"} for bit in port["bits"]}
    drivers = Counter()
    state_q = set()
    for cell in module.get("cells", {}).values():
        for port, direction in cell.get("port_directions", {}).items():
            if direction in {"output", "inout"}:
                bits = cell["connections"][port]
                drivers.update(bit for bit in bits if isinstance(bit, int))
                if port == "Q":
                    state_q.update(bits)
    result = {}
    for name, cell in module.get("cells", {}).items():
        if cell["type"] not in SCALAR_TYPES:
            continue
        outputs = [port for port, direction in cell.get("port_directions", {}).items()
                   if direction in {"output", "inout"}]
        bits = cell.get("connections", {}).get("Y", [])
        if outputs != ["Y"] or len(bits) != 1 or type(bits[0]) is not int:
            continue
        bit = bits[0]
        if bit not in inputs and bit not in state_q and drivers[bit] == 1:
            result[name] = bit
    return result


def scalar_constant_candidates(design: dict, top: str, pattern: str = ".*") -> list[dict]:
    """Enumerate both constants for eligible scalar nodes in a source cone."""
    eligible = _eligible_outputs(design, top)
    module = design["modules"][top]
    matches = re.compile(pattern)
    aliases = {}
    for name, net in module.get("netnames", {}).items():
        for bit in net["bits"]:
            if isinstance(bit, int):
                aliases.setdefault(bit, set()).add(name)
    candidates = []
    for name, bit in sorted(eligible.items()):
        cell = module["cells"][name]
        involved = {b for bits in cell["connections"].values() for b in bits
                    if isinstance(b, int)}
        nets = sorted({name for bit in involved for name in aliases.get(bit, ())})
        source = cell.get("attributes", {}).get("src")
        if not matches.search(" ".join([name, str(source), *nets])):
            continue
        for value in (0, 1):
            candidates.append({"kind": "scalar_output_constant", "cell": name,
                               "original_type": cell["type"], "output_bit": bit,
                               "constant": value, "source": source, "nets": nets})
    return candidates


def replace_scalar_constant(design: dict, top: str, candidate: dict) -> dict:
    """Replace exactly one scalar driver with a constant on the same wire."""
    eligible = _eligible_outputs(design, top)
    name = candidate["cell"]
    if (name not in eligible or candidate.get("output_bit") != eligible[name]
            or type(candidate.get("constant")) is not int or candidate["constant"] not in (0, 1)):
        raise ValueError("Candidate is not an eligible unique scalar driver")
    original = design["modules"][top]["cells"][name]
    if candidate.get("original_type") != original["type"]:
        raise ValueError("Candidate source cell changed")
    result = copy.deepcopy(design)
    cell = result["modules"][top]["cells"][name]
    cell["type"] = "$pos"
    cell["parameters"] = {"A_SIGNED": "0" * 32, "A_WIDTH": format(1, "032b"),
                          "Y_WIDTH": format(1, "032b")}
    cell["port_directions"] = {"A": "input", "Y": "output"}
    cell["connections"] = {"A": [str(candidate["constant"])], "Y": [eligible[name]]}
    return result
