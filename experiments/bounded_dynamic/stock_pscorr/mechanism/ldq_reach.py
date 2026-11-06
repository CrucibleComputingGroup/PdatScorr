#!/usr/bin/env python3
"""Exact reachable control states of ldq_top (TAG_LATENCY) by explicit-state search.

Mirrors ldq.sv and the TAG_LATENCY monitor cycle for cycle (request always accepted,
writeback always accepted, zero initial state = reset state, reset not re-applied:
re-reset only returns to the initial state). Data bits do not affect control, so
they are omitted. Prints which entries can ever be occupied and the maximum occupancy.
"""
from __future__ import annotations

import argparse
import json

FREE, WAIT_REQ, WAIT_RSP, DONE = range(4)


def lowest(st, value):
    for i, s in enumerate(st):
        if s == value:
            return i
    return None


def successors(state, n, lat):
    st, out, age = state
    alloc, req, wb = lowest(st, FREE), lowest(st, WAIT_REQ), lowest(st, DONE)
    for in_valid in (0, 1):
        for rsp in [None] + list(range(n)):
            if rsp is not None and not out[rsp]:
                continue
            if any(out[t] and age[t] >= lat and rsp != t for t in range(n)):
                continue
            nst = list(st)
            for i in range(n):
                if in_valid and alloc == i:
                    nst[i] = WAIT_REQ
                elif req == i:
                    nst[i] = WAIT_RSP
                elif rsp == i and st[i] == WAIT_RSP:
                    nst[i] = DONE
                elif wb == i:
                    nst[i] = FREE
            nout, nage = list(out), list(age)
            for t in range(n):
                if req == t:
                    nout[t], nage[t] = 1, 1
                elif rsp == t:
                    nout[t], nage[t] = 0, 0
                elif out[t]:
                    nage[t] = min(age[t] + 1, 15)
            yield (tuple(nst), tuple(nout), tuple(nage))


def explore(n: int, lat: int) -> dict:
    init = ((FREE,) * n, (0,) * n, (0,) * n)
    seen, frontier = {init}, [init]
    while frontier:
        nxt = []
        for s in frontier:
            for t in successors(s, n, lat):
                if t not in seen:
                    seen.add(t)
                    nxt.append(t)
        frontier = nxt
    used = sorted({i for st, _, _ in seen for i in range(n) if st[i] != FREE})
    return {"N": n, "LAT": lat, "states": len(seen), "entries_ever_occupied": used,
            "max_occupancy": max(sum(s != FREE for s in st) for st, _, _ in seen)}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--n", type=int, default=8)
    ap.add_argument("--lats", nargs="+", type=int, default=[1, 2, 3, 4])
    args = ap.parse_args()
    for lat in args.lats:
        print(json.dumps(explore(args.n, lat)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
