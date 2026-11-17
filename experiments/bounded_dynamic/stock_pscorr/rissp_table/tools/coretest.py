#!/usr/bin/env python3
"""Instruction-level functional test of the single-cycle RV32E core as an AIG.

Every instruction class is driven through the AIG with random operands and compared
against an RV32 reference: register results (read back through SW on dmem_wdata),
load/store addresses and strobes, and the next PC for branches and jumps.

Only LW, SW and the instruction under test are ever applied, so a netlist that was
optimized under an instruction-set constraint can be tested on its allowed set with
--allow.
"""
import argparse
import json
import random
import sys
sys.path.insert(0, sys.argv[0].rsplit("/", 1)[0])
from aigsim import read_aig, simulate, read_map

W = 128
MASK = (1 << W) - 1
M32 = 0xFFFFFFFF


def sx(v, bits=32):
    return v - (1 << bits) if v & (1 << (bits - 1)) else v


def ref_alu(name, a, b, simm):
    sh = b & 31
    shi = simm & 31
    u = simm & M32
    if name == "ADD": return (a + b) & M32
    if name == "SUB": return (a - b) & M32
    if name == "SLT": return int(sx(a) < sx(b))
    if name == "SLTU": return int(a < b)
    if name == "XOR": return a ^ b
    if name == "OR": return a | b
    if name == "AND": return a & b
    if name == "SLL": return (a << sh) & M32
    if name == "SRL": return a >> sh
    if name == "SRA": return (sx(a) >> sh) & M32
    if name == "ADDI": return (a + u) & M32
    if name == "SLTI": return int(sx(a) < sx(u))
    if name == "SLTIU": return int(a < u)
    if name == "XORI": return a ^ u
    if name == "ORI": return a | u
    if name == "ANDI": return a & u
    if name == "SLLI": return (a << shi) & M32
    if name == "SRLI": return a >> shi
    if name == "SRAI": return (sx(a) >> shi) & M32
    if name == "MUL": return (a * b) & M32
    if name == "MULH": return ((sx(a) * sx(b)) >> 32) & M32
    if name == "MULHSU": return ((sx(a) * b) >> 32) & M32
    if name == "MULHU": return (a * b) >> 32
    if name == "DIV":
        if b == 0: return M32
        if a == 0x80000000 and b == M32: return 0x80000000
        q = abs(sx(a)) // abs(sx(b))
        return (-q if (sx(a) < 0) != (sx(b) < 0) else q) & M32
    if name == "DIVU": return M32 if b == 0 else a // b
    if name == "REM":
        if b == 0: return a
        if a == 0x80000000 and b == M32: return 0
        r = abs(sx(a)) % abs(sx(b))
        return (-r if sx(a) < 0 else r) & M32
    if name == "REMU": return a if b == 0 else a % b
    raise ValueError(name)


def ref_branch(name, a, b):
    return {"BEQ": a == b, "BNE": a != b, "BLT": sx(a) < sx(b), "BGE": sx(a) >= sx(b),
            "BLTU": a < b, "BGEU": a >= b}[name]


R_OPS = {
    "ADD": (0x00, 0), "SUB": (0x20, 0), "SLL": (0x00, 1), "SLT": (0x00, 2), "SLTU": (0x00, 3),
    "XOR": (0x00, 4), "SRL": (0x00, 5), "SRA": (0x20, 5), "OR": (0x00, 6), "AND": (0x00, 7),
    "MUL": (0x01, 0), "MULH": (0x01, 1), "MULHSU": (0x01, 2), "MULHU": (0x01, 3),
    "DIV": (0x01, 4), "DIVU": (0x01, 5), "REM": (0x01, 6), "REMU": (0x01, 7),
}
I_OPS = {"ADDI": 0, "SLTI": 2, "SLTIU": 3, "XORI": 4, "ORI": 6, "ANDI": 7}
SH_OPS = {"SLLI": (0x00, 1), "SRLI": (0x00, 5), "SRAI": (0x20, 5)}
B_OPS = {"BEQ": 0, "BNE": 1, "BLT": 4, "BGE": 5, "BLTU": 6, "BGEU": 7}
LOADS = {"LB": 0, "LH": 1, "LW": 2, "LBU": 4, "LHU": 5}
STORES = {"SB": 0, "SH": 1, "SW": 2}

GROUPS = {
    "mul": ["MUL", "MULH", "MULHSU", "MULHU"],
    "div": ["DIV", "DIVU", "REM", "REMU"],
    "add": ["ADD", "ADDI", "SUB", "SLT", "SLTI", "SLTU", "SLTIU"],
    "shift": ["SLL", "SLLI", "SRL", "SRLI", "SRA", "SRAI"],
    "logic": ["XOR", "XORI", "OR", "ORI", "AND", "ANDI"],
    "upper": ["LUI", "AUIPC"],
    "mem": ["LB", "LH", "LW", "LBU", "LHU", "SB", "SH", "SW"],
    "branch": ["BEQ", "BNE", "BLT", "BGE", "BLTU", "BGEU"],
    "jump": ["JAL", "JALR"],
    "seq": ["PC+4"],
}
ORDER = ["logic", "add", "shift", "mul", "div", "upper", "mem", "branch", "jump", "seq"]

LW_X1 = 0x00002083   # lw x1, 0(x0)
LW_X2 = 0x00002103   # lw x2, 0(x0)
SW_X3 = 0x00302023   # sw x3, 0(x0)
RD, RS1, RS2 = 3, 1, 2


def enc_i(imm, rs1, f3, rd, opc):
    return ((imm & 0xFFF) << 20) | (rs1 << 15) | (f3 << 12) | (rd << 7) | opc


def enc_s(imm, rs2, rs1, f3):
    imm &= 0xFFF
    return ((imm >> 5) << 25) | (rs2 << 20) | (rs1 << 15) | (f3 << 12) | ((imm & 31) << 7) | 0x23


def enc_b(off, rs2, rs1, f3):
    o = off & 0x1FFF
    return (((o >> 12) & 1) << 31) | (((o >> 5) & 0x3F) << 25) | (rs2 << 20) | (rs1 << 15) | \
           (f3 << 12) | (((o >> 1) & 0xF) << 8) | (((o >> 11) & 1) << 7) | 0x63


def enc_j(off, rd):
    o = off & 0x1FFFFF
    return (((o >> 20) & 1) << 31) | (((o >> 1) & 0x3FF) << 21) | (((o >> 11) & 1) << 20) | \
           (((o >> 12) & 0xFF) << 12) | (rd << 7) | 0x6F


def spread(values, bit):
    w = 0
    for p, v in enumerate(values):
        if (v >> bit) & 1:
            w |= 1 << p
    return w


class Core:
    def __init__(self, aig_path, map_path):
        self.aig = read_aig(aig_path)
        self.ins, self.outs = read_map(map_path)
        self.rst = "rst_n" if "rst_n" in self.ins else "rst"

    def run(self, instrs, datas, seed=5):
        """instrs: per-frame instruction word (same for all patterns).
        datas: per-frame list of W dmem_rdata values, or None for random."""
        rnd = random.Random(seed)
        frames = []
        for instr, d in zip(instrs, datas):
            fin = [rnd.getrandbits(W) for _ in range(self.aig["I"])]
            for b in range(32):
                fin[self.ins["imem_rdata"][b]] = MASK if (instr >> b) & 1 else 0
                fin[self.ins["dmem_rdata"][b]] = spread(d, b) if d is not None else rnd.getrandbits(W)
            fin[self.ins[self.rst][0]] = MASK
            frames.append(fin)
        res, cons = simulate(self.aig, frames, W)
        self.cons = cons
        return res

    def word(self, frame_out, name, bits=32):
        vals = []
        o = self.outs[name]
        for p in range(W):
            v = 0
            for b in range(bits):
                if (frame_out[o[b]] >> p) & 1:
                    v |= 1 << b
            vals.append(v)
        return vals


def operands(rnd):
    A, B = [], []
    special = [0, 1, 2, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0xFFFFFFFE, 31, 32, 0x55555555]
    for p in range(W):
        if p < 50:
            A.append(special[p % len(special)])
            B.append(special[(p // len(special) + p) % len(special)])
        else:
            A.append(rnd.getrandbits(rnd.choice([8, 16, 31, 32, 32])))
            B.append(rnd.getrandbits(rnd.choice([3, 5, 8, 16, 32, 32])))
    return A, B


def count(got, exp):
    return sum(1 for g, e in zip(got, exp) if g == e), len(exp)


def test_instruction(core, name, A, B):
    ok = tot = 0

    def add(c):
        nonlocal ok, tot
        ok += c[0]
        tot += c[1]

    if name in R_OPS or name in I_OPS or name in SH_OPS:
        imms = [0] if name in R_OPS else [5, 0x7FF, 0xFFF, 17, 0x800]
        for imm in imms:
            simm = sx(imm, 12)
            if name in R_OPS:
                f7, f3 = R_OPS[name]
                instr = (f7 << 25) | (RS2 << 20) | (RS1 << 15) | (f3 << 12) | (RD << 7) | 0x33
            elif name in I_OPS:
                instr = enc_i(imm, RS1, I_OPS[name], RD, 0x13)
            else:
                f7, f3 = SH_OPS[name]
                instr = (f7 << 25) | ((imm & 31) << 20) | (RS1 << 15) | (f3 << 12) | (RD << 7) | 0x13
            res = core.run([LW_X1, LW_X2, instr, SW_X3], [A, B, None, None])
            add(count(core.word(res[3], "dmem_wdata"), [ref_alu(name, a, b, simm) for a, b in zip(A, B)]))
            add(count(core.word(res[3], "imem_addr"), [(p + 4) & M32 for p in core.word(res[2], "imem_addr")]))
    elif name == "LUI":
        for imm20 in (0x12345, 0xFFFFF, 0x80000, 1):
            instr = (imm20 << 12) | (RD << 7) | 0x37
            res = core.run([instr, SW_X3], [None, None])
            add(count(core.word(res[1], "dmem_wdata"), [(imm20 << 12) & M32] * W))
    elif name == "AUIPC":
        for imm20 in (0x12345, 0xFFFFF, 0x80000, 1):
            instr = (imm20 << 12) | (RD << 7) | 0x17
            res = core.run([instr, SW_X3], [None, None])
            pc0 = core.word(res[0], "imem_addr")
            add(count(core.word(res[1], "dmem_wdata"), [(p + (imm20 << 12)) & M32 for p in pc0]))
    elif name in LOADS:
        for imm in (0, 4, 0x7FF, 0xFFC, 0x800):
            simm = sx(imm, 12)
            instr = enc_i(imm, RS1, LOADS[name], RD, 0x03)
            res = core.run([LW_X1, instr, SW_X3], [A, B, None])
            add(count(core.word(res[1], "dmem_addr"), [(a + simm) & M32 for a in A]))
            add(count(core.word(res[1], "dmem_re", 1), [1] * W))
            add(count(core.word(res[1], "dmem_we", 1), [0] * W))
            # the core forwards the memory word unchanged (byte selection is left to the memory)
            add(count(core.word(res[2], "dmem_wdata"), B))
    elif name in STORES:
        for imm in (0, 4, 0x7FF, 0xFFC, 0x800):
            simm = sx(imm, 12)
            instr = enc_s(imm, RS2, RS1, STORES[name])
            res = core.run([LW_X1, LW_X2, instr], [A, B, None])
            add(count(core.word(res[2], "dmem_addr"), [(a + simm) & M32 for a in A]))
            add(count(core.word(res[2], "dmem_wdata"), B))
            add(count(core.word(res[2], "dmem_we", 1), [1] * W))
            add(count(core.word(res[2], "dmem_re", 1), [0] * W))
    elif name in B_OPS:
        for off in (8, -8, 0xFFE, -0x1000, 64):
            instr = enc_b(off, RS2, RS1, B_OPS[name])
            res = core.run([LW_X1, LW_X2, instr, SW_X3], [A, B, None, None])
            pc2 = core.word(res[2], "imem_addr")
            exp = [((p + off) if ref_branch(name, a, b) else (p + 4)) & M32 for p, a, b in zip(pc2, A, B)]
            add(count(core.word(res[3], "imem_addr"), exp))
            add(count(core.word(res[2], "dmem_we", 1), [0] * W))
    elif name == "JAL":
        for off in (8, -8, 0xFFFFE, -0x100000, 2048):
            instr = enc_j(off, RD)
            res = core.run([instr, SW_X3], [None, None])
            pc0 = core.word(res[0], "imem_addr")
            add(count(core.word(res[1], "imem_addr"), [(p + off) & M32 for p in pc0]))
            add(count(core.word(res[1], "dmem_wdata"), [(p + 4) & M32 for p in pc0]))
    elif name == "JALR":
        for imm in (0, 4, 0x7FF, 0xFFD, 0x800):
            simm = sx(imm, 12)
            instr = enc_i(imm, RS1, 0, RD, 0x67)
            res = core.run([LW_X1, instr, SW_X3], [A, None, None])
            pc1 = core.word(res[1], "imem_addr")
            add(count(core.word(res[2], "imem_addr"), [((a + simm) & M32) & ~1 for a in A]))
            add(count(core.word(res[2], "dmem_wdata"), [(p + 4) & M32 for p in pc1]))
    elif name == "PC+4":
        res = core.run([LW_X1, LW_X2, SW_X3, LW_X1], [A, B, None, None])
        for f in range(3):
            add(count(core.word(res[f + 1], "imem_addr"), [(p + 4) & M32 for p in core.word(res[f], "imem_addr")]))
    else:
        raise ValueError(name)
    return ok, tot


def allowed_set(spec):
    """spec like 'mul=1,div=0,add=1,shift=0' -> instruction names allowed."""
    flags = dict(kv.split("=") for kv in spec.split(","))
    names = []
    for g in ORDER:
        if g in flags and flags[g] == "0":
            continue
        names += GROUPS[g]
    return names


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--map", required=True)
    ap.add_argument("--allow", default="", help="e.g. mul=1,div=0,add=1,shift=0 (default: test everything)")
    ap.add_argument("--json", default="")
    ap.add_argument("aigs", nargs="+")
    a = ap.parse_args()
    names = allowed_set(a.allow) if a.allow else [n for g in ORDER for n in GROUPS[g]]
    rnd = random.Random(11)
    A, B = operands(rnd)
    report = {}
    for path in a.aigs:
        core = Core(path, a.map)
        res = {n: test_instruction(core, n, A, B) for n in names}
        report[path] = {n: {"ok": r[0], "total": r[1]} for n, r in res.items()}
        bad = [n for n in names if res[n][0] != res[n][1]]
        print("%s  ands=%d  tested=%d  failing=%d" % (path, core.aig["A"], len(names), len(bad)))
        for g in ORDER:
            row = [n for n in GROUPS[g] if n in res]
            if row:
                print("   %-6s" % g, "  ".join("%s %s" % (n, "ok" if res[n][0] == res[n][1] else "FAIL(%d/%d)" % res[n]) for n in row))
    if a.json:
        with open(a.json, "w") as f:
            json.dump(report, f, indent=1)


if __name__ == "__main__":
    main()
