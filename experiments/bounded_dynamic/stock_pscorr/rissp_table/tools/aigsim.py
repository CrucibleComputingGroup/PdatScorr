#!/usr/bin/env python3
"""Bit-parallel simulator for binary AIGER files (zero-initialized latches).

Used to run concrete RISC-V instruction sequences through the single-cycle core's
AIG before and after optimization and compare the observable outputs.
"""
import random
import sys


def read_aig(path):
    with open(path, "rb") as f:
        data = f.read()
    pos = data.index(b"\n")
    hdr = data[:pos].split()
    assert hdr[0] == b"aig", hdr
    M, I, L, O, A = (int(x) for x in hdr[1:6])
    extra = [int(x) for x in hdr[6:]]  # B C J F (constraints etc.)
    pos += 1
    latch_next = []
    for _ in range(L):
        end = data.index(b"\n", pos)
        toks = data[pos:end].split()
        latch_next.append(int(toks[0]))
        if len(toks) > 1:
            assert toks[1] == b"0", "non-zero latch reset not supported: %r" % toks
        pos = end + 1
    outs = []
    for _ in range(O):
        end = data.index(b"\n", pos)
        outs.append(int(data[pos:end]))
        pos = end + 1
    extra_lits = []
    for n in extra:
        for _ in range(n):
            end = data.index(b"\n", pos)
            extra_lits.append(int(data[pos:end]))
            pos = end + 1
    ands = []
    for i in range(A):
        lhs = 2 * (I + L + i + 1)
        d0 = 0
        shift = 0
        while True:
            b = data[pos]
            pos += 1
            d0 |= (b & 0x7F) << shift
            shift += 7
            if not b & 0x80:
                break
        d1 = 0
        shift = 0
        while True:
            b = data[pos]
            pos += 1
            d1 |= (b & 0x7F) << shift
            shift += 7
            if not b & 0x80:
                break
        r0 = lhs - d0
        r1 = r0 - d1
        ands.append((r0, r1))
    return dict(M=M, I=I, L=L, O=O, A=A, latch_next=latch_next, outs=outs,
                ands=ands, extra=extra, extra_lits=extra_lits)


def simulate(aig, frames_inputs, width):
    """frames_inputs: list (per frame) of lists of I ints (bit-parallel words).
    Returns list (per frame) of lists of O ints, plus constraint outputs."""
    mask = (1 << width) - 1
    I, L = aig["I"], aig["L"]
    ands = aig["ands"]
    latch = [0] * L
    results = []
    cons = []
    val = [0] * (aig["M"] + 1)
    for fin in frames_inputs:
        val[0] = 0
        for i in range(I):
            val[1 + i] = fin[i]
        for i in range(L):
            val[1 + I + i] = latch[i]
        base = 1 + I + L
        for k, (r0, r1) in enumerate(ands):
            a = val[r0 >> 1]
            if r0 & 1:
                a ^= mask
            b = val[r1 >> 1]
            if r1 & 1:
                b ^= mask
            val[base + k] = a & b

        def lit(l):
            v = val[l >> 1]
            return v ^ mask if l & 1 else v

        results.append([lit(o) for o in aig["outs"]])
        cons.append([lit(o) for o in aig["extra_lits"]])
        latch = [lit(n) for n in aig["latch_next"]]
    return results, cons


def read_map(path):
    ins, outs = {}, {}
    with open(path) as f:
        for line in f:
            t = line.split()
            if not t:
                continue
            if t[0] == "input":
                ins.setdefault(t[3], {})[int(t[2])] = int(t[1])
            elif t[0] == "output":
                outs.setdefault(t[3], {})[int(t[2])] = int(t[1])
    return ins, outs
