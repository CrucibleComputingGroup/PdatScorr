#!/usr/bin/env python3
"""Product machine of two AIGs of the same core for the error-injection proof.

Both AIGs come from the flow's Yosys script with zero-initialized flip-flops (the reset
state) and carry the instruction constraint as an AIGER constraint. The product shares
all primary inputs. Its outputs are the disagreements at the architectural observation
boundary, one per observed bit; each must be constant 0. The constraint of the original
design is kept as the constraint of the product.
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "tools"))
from aigsim import read_aig, read_map  # noqa: E402


class Builder:
    def __init__(self, n_inputs, n_latches):
        self.I = n_inputs
        self.L = n_latches
        self.ands = []          # (rhs0, rhs1) in the product's numbering
        self.cache = {}

    def new_and(self, a, b):
        if a < b:
            a, b = b, a
        if b == 0 or a == (b ^ 1):
            return 0
        if b == 1:
            return a
        if a == b:
            return a
        key = (a, b)
        if key not in self.cache:
            self.ands.append(key)
            self.cache[key] = 2 * (self.I + self.L + len(self.ands))
        return self.cache[key]

    def raw_and(self, a, b):
        """Append an AND without simplification (keeps the source AIG's numbering dense)."""
        if a < b:
            a, b = b, a
        self.ands.append((a, b))
        return 2 * (self.I + self.L + len(self.ands))

    def new_or(self, a, b):
        return self.new_and(a ^ 1, b ^ 1) ^ 1

    def new_xor(self, a, b):
        return self.new_or(self.new_and(a, b ^ 1), self.new_and(a ^ 1, b))


def encode(delta):
    out = bytearray()
    while delta & ~0x7F:
        out.append((delta & 0x7F) | 0x80)
        delta >>= 7
    out.append(delta)
    return bytes(out)


def build(gold_path, gate_path, portmap, boundary, out_path, strict=False):
    gold, gate = read_aig(gold_path), read_aig(gate_path)
    ins, outs = read_map(portmap)
    I = gold["I"]
    assert gate["I"] == I, "the two AIGs must have the same primary inputs"
    assert len(gold["outs"]) == len(gate["outs"])
    assert len(gold["extra_lits"]) == 1 and len(gate["extra_lits"]) == 1, "expected one constraint each"
    Lg, Lt = gold["L"], gate["L"]
    b = Builder(I, Lg + Lt)

    def mapper(aig, latch_offset):
        table = {}                       # source AND variable -> product literal
        first_and = 1 + aig["I"] + aig["L"]

        def lit(l):
            v, s = l >> 1, l & 1
            if v == 0:
                return s
            if v <= I:
                return l
            if v < first_and:
                return 2 * (v + latch_offset) | s
            return table[v] ^ s

        for k, (r0, r1) in enumerate(aig["ands"]):
            table[first_and + k] = b.raw_and(lit(r0), lit(r1))
        return lit

    lit_g = mapper(gold, 0)
    lit_t = mapper(gate, Lg)
    latch_next = [lit_g(n) for n in gold["latch_next"]] + [lit_t(n) for n in gate["latch_next"]]

    def out(lit_fn, aig, name, bit):
        return lit_fn(aig["outs"][outs[name][bit]])

    props, labels = [], []

    def compare(name, qualifier=1):
        for bit in sorted(outs[name]):
            d = b.new_xor(out(lit_g, gold, name, bit), out(lit_t, gate, name, bit))
            props.append(b.new_and(qualifier, d))
            labels.append("%s[%d]" % (name, bit))

    for name in boundary["every_cycle"]:
        compare(name)
    for group in boundary["when_requested"]:
        q = 0
        for r in group["request"]:
            q = b.new_or(q, out(lit_g, gold, r, 0))
        for name in group["signals"]:
            compare(name, 1 if strict else q)

    constraint = lit_g(gold["extra_lits"][0])
    n_ands = len(b.ands)
    M = I + Lg + Lt + n_ands
    with open(out_path, "wb") as f:
        f.write(b"aig %d %d %d %d %d 0 1 0 0\n" % (M, I, Lg + Lt, len(props), n_ands))
        for n in latch_next:
            f.write(b"%d\n" % n)
        for p in props:
            f.write(b"%d\n" % p)
        f.write(b"%d\n" % constraint)
        for k, (r0, r1) in enumerate(b.ands):
            lhs = 2 * (I + Lg + Lt + k + 1)
            assert lhs > r0 >= r1, (lhs, r0, r1)
            f.write(encode(lhs - r0))
            f.write(encode(r0 - r1))
    return labels


def proved_outputs(aig_path, n_props):
    """Indices of the disagreement outputs that are not the constant 0 in an AIG written by ABC.
    ABC writes them either as outputs or as bad-state properties, before the constraint."""
    aig = read_aig(aig_path)
    lits = aig["outs"] + aig["extra_lits"]
    assert len(lits) >= n_props, "unexpected output count in %s" % aig_path
    return [i for i in range(n_props) if lits[i] != 0]
