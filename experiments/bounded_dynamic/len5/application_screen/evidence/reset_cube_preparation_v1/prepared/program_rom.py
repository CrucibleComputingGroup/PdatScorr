"""Decode the experiment's byte-addressed Verilog image into an immutable ROM.

The ROM is an explicit instruction-side platform model. Data-side read values
remain independently symbolic in the admission harness. Instruction addresses
are outputs of the original core; no PC sequence or executable-range assumption
is introduced. Misaligned and unmapped requests return instruction exceptions.
"""
from __future__ import annotations

import hashlib
from pathlib import Path
import re


def read_image(path: Path) -> dict:
    raw = path.read_bytes()
    source = re.sub(r"/\*.*?\*/|//[^\n]*", "", raw.decode("ascii"), flags=re.S)
    address = None
    memory = {}
    for token in source.split():
        if token.startswith("@"):
            if not re.fullmatch(r"@[0-9a-fA-F]+", token):
                raise ValueError(f"Malformed address token: {token}")
            address = int(token[1:], 16)
        else:
            if address is None or not re.fullmatch(r"[0-9a-fA-F]{2}", token):
                raise ValueError(f"Expected addressed byte: {token}")
            if address in memory:
                raise ValueError("Repeated image address")
            memory[address] = int(token, 16)
            address += 1
    if not memory or min(memory) != 0 or sorted(memory) != list(range(len(memory))):
        raise ValueError("ROM v1 requires a contiguous image starting at zero")
    if len(memory) % 4:
        raise ValueError("ROM image length must contain complete 32-bit words")
    words = {address: sum(memory[address+i] << (8*i) for i in range(4))
             for address in range(0, len(memory), 4)}
    return {"image_sha256": hashlib.sha256(raw).hexdigest(), "bytes": len(memory),
            "words": words, "nonzero_words": sum(bool(word) for word in words.values()),
            "byte_order": "little", "immutable_instruction_image": True,
            "unmapped_exception_code": 1, "misaligned_exception_code": 0,
            "successful_exception_code": 31}


def response(image: dict, address: int, fault_data: int = 0) -> tuple[int, bool, int]:
    """Concrete oracle for tests and finite native trace replay."""
    if address & 3:
        return fault_data, True, 0
    if address not in image["words"]:
        return fault_data, True, 1
    return image["words"][address], False, 31


def verilog_selector(image: dict, zero_fault_data: bool = False) -> list[str]:
    """Define the request payload without constraining the requested address."""
    words = image["words"]
    if set(words) != set(range(0, image["bytes"], 4)):
        raise ValueError("Incomplete ROM word map")
    lines = [
        "  always @* begin",
        "    selected_instruction = " + ("32'b0;" if zero_fault_data else "instruction_fault_data;"),
        "    selected_instruction_fault = 1; selected_instruction_code = 1;",
        "    if (instr_addr_o[1:0] != 0) selected_instruction_code = 0;",
        f"    else if (instr_addr_o < 64'd{image['bytes']}) begin",
        "      selected_instruction = 0;",
        "      selected_instruction_fault = 0; selected_instruction_code = 31;",
        "      case (instr_addr_o)"]
    for address, word in sorted(words.items()):
        if word:
            lines.append(f"        64'h{address:016x}: selected_instruction = 32'h{word:08x};")
    lines += ["        default: ;", "      endcase", "    end", "  end"]
    return lines
