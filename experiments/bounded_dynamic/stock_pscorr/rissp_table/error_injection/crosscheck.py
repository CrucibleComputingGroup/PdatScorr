#!/usr/bin/env python3
"""Independent check of an error-injection proof by constrained-random simulation.

  crosscheck.py PRODUCT.aig GOLD.portmap ASSUMPTIONS.sv [--cycles N] [--seed S]

Simulates the product machine of miter.py from the reset state with random permitted
instructions, random memory data and occasional reset pulses during which the instruction
is arbitrary (the generated constraint exempts reset). Reports whether the constraint held
in every simulated cycle and the first cycle, if any, in which a disagreement output is 1.
A proved injection must show no disagreement; a rejected one is expected to show one.
"""
import argparse
import os
import random
import re
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "tools"))
from aigsim import read_aig, read_map  # noqa: E402
import coretest as ct  # noqa: E402

W = 64
MASK = (1 << W) - 1


def encode(name, rnd):
    rd, rs1, rs2 = rnd.randrange(32), rnd.randrange(32), rnd.randrange(32)
    imm = rnd.getrandbits(12)
    if name in ct.R_OPS:
        f7, f3 = ct.R_OPS[name]
        return (f7 << 25) | (rs2 << 20) | (rs1 << 15) | (f3 << 12) | (rd << 7) | 0x33
    if name in ct.I_OPS:
        return ct.enc_i(imm, rs1, ct.I_OPS[name], rd, 0x13)
    if name in ct.SH_OPS:
        f7, f3 = ct.SH_OPS[name]
        return (f7 << 25) | ((imm & 31) << 20) | (rs1 << 15) | (f3 << 12) | (rd << 7) | 0x13
    if name in ct.LOADS:
        return ct.enc_i(imm, rs1, ct.LOADS[name], rd, 0x03)
    if name in ct.STORES:
        return ct.enc_s(imm, rs2, rs1, ct.STORES[name])
    if name in ct.B_OPS:
        return ct.enc_b(rnd.getrandbits(12) << 1, rs2, rs1, ct.B_OPS[name])
    if name == "JAL":
        return ct.enc_j(rnd.getrandbits(20) << 1, rd)
    if name == "JALR":
        return ct.enc_i(imm, rs1, 0, rd, 0x67)
    if name == "LUI":
        return (rnd.getrandbits(20) << 12) | (rd << 7) | 0x37
    if name == "AUIPC":
        return (rnd.getrandbits(20) << 12) | (rd << 7) | 0x17
    if name == "ECALL":
        return 0x00000073
    if name == "EBREAK":
        return 0x00100073
    if name == "FENCE":
        return (rnd.getrandbits(12) << 20) | (rs1 << 15) | (rd << 7) | 0x0F
    raise ValueError(name)


def simulate_product(product, portmap, assumptions, cycles=400, seed=1):
    aig = read_aig(product)
    ins, _ = read_map(portmap)
    permitted = sorted(set(re.findall(r"//\s*([A-Z]+)\s*$", open(assumptions).read(), re.M)))
    rnd = random.Random(seed)
    rst = "rst_n" if "rst_n" in ins else "rst"
    I, L = aig["I"], aig["L"]
    base = 1 + I + L
    latch = [0] * L
    val = [0] * (aig["M"] + 1)
    first_bad = None
    constraint_ok = True
    executed = 0
    for cycle in range(cycles):
        fin = [0] * I
        in_reset = [rnd.random() < 0.02 for _ in range(W)]
        words, data = [], []
        for p in range(W):
            if in_reset[p]:
                words.append(rnd.getrandbits(32))            # arbitrary while reset is asserted
            else:
                words.append(encode(rnd.choice(permitted), rnd))
                executed += 1
            # memory data: mostly random, sometimes small or zero (exercises division by zero)
            r = rnd.random()
            data.append(0 if r < 0.1 else rnd.getrandbits(4) if r < 0.3 else rnd.getrandbits(32))
        for b in range(32):
            fin[ins["imem_rdata"][b]] = ct.spread(words, b)
            fin[ins["dmem_rdata"][b]] = ct.spread(data, b)
        fin[ins[rst][0]] = sum((0 if in_reset[p] else 1) << p for p in range(W))
        for i in range(I):
            val[1 + i] = fin[i]
        for i in range(L):
            val[1 + I + i] = latch[i]
        for k, (r0, r1) in enumerate(aig["ands"]):
            x = val[r0 >> 1]
            if r0 & 1:
                x ^= MASK
            y = val[r1 >> 1]
            if r1 & 1:
                y ^= MASK
            val[base + k] = x & y

        def lit(l):
            v = val[l >> 1]
            return v ^ MASK if l & 1 else v

        if lit(aig["extra_lits"][-1]) != MASK:
            constraint_ok = False
        bad = 0
        for o in aig["outs"]:
            bad |= lit(o)
        if bad and first_bad is None:
            first_bad = cycle
            break
        latch = [lit(n) for n in aig["latch_next"]]
    return {"cycles": cycles, "traces": W, "permitted_instructions_executed": executed,
            "constraint_held": constraint_ok, "first_disagreement_cycle": first_bad}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("product")
    ap.add_argument("portmap")
    ap.add_argument("assumptions")
    ap.add_argument("--cycles", type=int, default=400)
    ap.add_argument("--seed", type=int, default=1)
    a = ap.parse_args()
    r = simulate_product(a.product, a.portmap, a.assumptions, a.cycles, a.seed)
    print("%s: %d cycles x %d traces, %d permitted instructions executed, constraint held: %s, disagreement: %s" % (
        os.path.basename(a.product), r["cycles"], r["traces"], r["permitted_instructions_executed"],
        "yes" if r["constraint_held"] else "NO",
        "none" if r["first_disagreement_cycle"] is None else "first in cycle %d" % r["first_disagreement_cycle"]))
    return 0 if r["constraint_held"] else 2


if __name__ == "__main__":
    sys.exit(main())
