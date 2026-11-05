"""Apply only the declared external instruction-memory lookup replacement."""
from pathlib import Path

HERE = Path(__file__).resolve().parent
START = b"  always_comb begin : p_ins_mem_req\n"
END = b"  // Instruction address register\n"


def patch_memory(raw: bytes) -> bytes:
    assert raw.count(START) == raw.count(END) == 1
    start, end = raw.index(START), raw.index(END)
    assert start < end
    # Keep all upstream logic outside this original combinational lookup block.
    # The replacement adds a separate ROM object; data ports still access mem.
    replacement = (HERE / "harvard_lookup.svh").read_bytes()
    assert b".Write" not in replacement
    result = raw[:start] + replacement + b"\n" + raw[end:]
    assert result[:start] == raw[:start] and result.endswith(raw[end:])
    return result
