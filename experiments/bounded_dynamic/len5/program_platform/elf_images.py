"""Extract Harvard images by ELF section flags, checked against load segments.

No opcode whitelist selects image bytes. Only SHF_ALLOC/SHF_EXECINSTR and the
matching PT_LOAD flags determine executable versus data contents.
"""
from __future__ import annotations
import hashlib
from pathlib import Path
import struct


def sha(data): return hashlib.sha256(data).hexdigest()


def read_hex(path: Path) -> dict[int, int]:
    result, address = {}, None
    for line in path.read_text().splitlines():
        for token in line.split("//", 1)[0].split():
            if token.startswith("@"):
                address = int(token[1:], 16)
            else:
                assert address is not None and address not in result
                value = int(token, 16); assert 0 <= value < 256
                result[address] = value; address += 1
    return result


def write_hex(path: Path, values: dict[int, int]):
    rows, line, previous = [], [], None
    for address, value in sorted(values.items()):
        if previous is None or address != previous + 1:
            if line: rows.append(" ".join(line)); line = []
            rows.append(f"@{address:08X}")
        line.append(f"{value:02X}")
        if len(line) == 16: rows.append(" ".join(line)); line = []
        previous = address
    if line: rows.append(" ".join(line))
    path.write_text("\n".join(rows) + "\n")
    assert read_hex(path) == values


def executable_images(path: Path):
    data = path.read_bytes()
    h = struct.unpack_from("<16sHHIQQQIHHHHHH", data)
    ident, etype, machine, version, entry, phoff, shoff, flags, ehsize, phsize, phnum, shsize, shnum, shstr = h
    assert ident[:6] == b"\x7fELF\x02\x01" and etype == 2 and machine == 243 and version == 1
    assert ehsize == 64 and phsize == 56 and shsize == 64 and shnum and shstr < shnum
    segments = []
    for i in range(phnum):
        t, f, off, addr, physical, size, memsize, alignment = struct.unpack_from("<IIQQQQQQ", data, phoff + i * phsize)
        if t == 1:
            assert off + size <= len(data) and memsize >= size and addr == physical
            segments.append({"flags": f, "offset": off, "address": addr, "size": size, "memory_size": memsize})
    sections = [struct.unpack_from("<IIQQQQIIQQ", data, shoff + i * shsize) for i in range(shnum)]
    names_section = sections[shstr]
    strings = data[names_section[4]:names_section[4]+names_section[5]]
    instruction, ram, records = {}, {}, []
    for s in sections:
        name_off, kind, sf, addr, off, size, link, info, align, entsize = s
        name = strings[name_off:].split(b"\0", 1)[0].decode()
        if not (sf & 2) or size == 0: continue
        assert kind in (1, 8), f"Unsupported allocated section {name} type {kind}"
        executable = bool(sf & 4)
        assert not (executable and kind == 8), "Uninitialized executable bytes unsupported"
        matches = [p for p in segments if p["address"] <= addr and addr + size <= p["address"] + p["memory_size"]]
        assert len(matches) == 1 and bool(matches[0]["flags"] & 1) == executable
        segment = matches[0]
        if kind == 1:
            assert off + size <= len(data)
            assert segment["offset"] + addr - segment["address"] == off
            assert addr + size <= segment["address"] + segment["size"]
        content = data[off:off + size] if kind == 1 else bytes(size)
        target = instruction if executable else ram
        for index, byte in enumerate(content):
            assert addr + index not in target
            target[addr + index] = byte
        records.append({"name": name, "type": kind, "flags": sf, "address": addr,
                        "size": size, "executable": executable, "segment_flags": segment["flags"],
                        "content_sha256": sha(content)})
    assert entry in instruction and not set(instruction).intersection(ram)
    return instruction, ram, {"elf_sha256": sha(data), "entry": entry,
        "selection_rule": "All allocated ELF sections; SHF_EXECINSTR selects instruction ROM; PT_LOAD PF_X must agree",
        "sections": records, "load_segments": segments}
