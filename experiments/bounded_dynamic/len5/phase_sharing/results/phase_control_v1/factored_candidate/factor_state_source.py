"""Certified common-state reduction for an explicit initial-reset miter.

Reference state keeps its real transition. Matched candidate Q is shared only
with a proof obligation comparing both ORIGINAL effective next-state values.
Native reset gives the base relation; the obligations give its inductive step.
No state is replaced by fresh values and no equality assumption is added.
"""
from __future__ import annotations
from odc.temporal import parameter_int


def factor_common_state(design, top, pairs, *, reset_port="rst_ni"):
    mod = design["modules"][top]
    reset = mod["ports"][reset_port]
    if reset["direction"] != "input" or len(reset["bits"]) != 1:
        raise ValueError("Expected scalar native reset input")
    rst = reset["bits"]
    drivers = {}
    for name, cell in mod["cells"].items():
        for port, direction in cell["port_directions"].items():
            if direction != "output":
                continue
            for bit in cell["connections"][port]:
                if not isinstance(bit, int):
                    continue
                if bit in drivers:
                    raise ValueError("Multiple cell drivers in factoring input")
                drivers[bit] = (name, cell)
    assumptions = [c for c in mod["cells"].values() if c["type"] == "$assume"]
    if len(assumptions) != 1:
        raise ValueError("Factoring v1 requires exactly the immutable initial-reset assumption")
    premise = assumptions[0]["connections"]
    a = drivers[premise["A"][0]][1]
    e = drivers[premise["EN"][0]][1]
    if a["type"] != "$logic_not" or a["connections"]["A"] != rst:
        raise ValueError("Initial premise must assert native active-low reset")
    if e["type"] == "$mux" and e["connections"]["A"] == ["0"] and e["connections"]["B"] == ["1"]:
        e = drivers[e["connections"]["S"][0]][1]
    if e["type"] != "$initstate":
        raise ValueError("Reset premise must be enabled exactly by initstate")
    qdriver = {}
    for name, cell in mod["cells"].items():
        if cell["type"] in ("$adff", "$adffe"):
            for i, bit in enumerate(cell["connections"]["Q"]):
                if bit in qdriver:
                    raise ValueError("Multiple native FF drivers")
                qdriver[bit] = (name, cell, i)
    if len({r for r, c in pairs}) != len(pairs) or len({c for r, c in pairs}) != len(pairs):
        raise ValueError("Factoring requires one-to-one Q pairs")
    alias = {c: r for r, c in pairs}
    if set(alias) & set(alias.values()):
        raise ValueError("Reference/candidate state sets overlap")
    for r, c in pairs:
        _, a, ai = qdriver[r]
        _, b, bi = qdriver[c]
        for cell in (a, b):
            if cell["connections"]["ARST"] != rst or parameter_int(cell["parameters"]["ARST_POLARITY"]) != 0:
                raise ValueError("Every factored state bit must use the initial native reset directly")
        if (a["connections"]["CLK"] != b["connections"]["CLK"]
                or parameter_int(a["parameters"]["CLK_POLARITY"]) != parameter_int(b["parameters"]["CLK_POLARITY"])):
            raise ValueError("Factored clocks must match")
        av = a["parameters"]["ARST_VALUE"][::-1][ai]
        bv = b["parameters"]["ARST_VALUE"][::-1][bi]
        if av not in ("0", "1") or bv not in ("0", "1"):
            raise ValueError("Factoring requires defined reset values")
        if av != bv:
            raise ValueError("Factored reset values must match bitwise")
    prefix = "$pscorr_factored_"
    if any(n.startswith(prefix) for n in mod["cells"]):
        raise ValueError("Factoring already applied")
    nextbit = max(bit for cell in mod["cells"].values() for bs in cell["connections"].values()
                  for bit in bs if isinstance(bit, int)) + 1
    serial = 0

    def add(kind, connections, params, dirs):
        nonlocal serial
        serial += 1
        mod["cells"][prefix + str(serial)] = {"hide_name": 1, "type": kind, "parameters": params,
            "attributes": {"pscorr_proof_only": 1}, "port_directions": dirs, "connections": connections}

    def fresh(width=1):
        nonlocal nextbit
        bits = list(range(nextbit, nextbit + width))
        nextbit += width
        return bits

    def mux(a, b, s):
        y = fresh(len(a))
        add("$mux", {"A": a, "B": b, "S": s, "Y": y}, {"WIDTH": len(a)},
            {"A": "input", "B": "input", "S": "input", "Y": "output"})
        return y

    cached = {}
    def effective_next(name, cell):
        if name in cached:
            return cached[name]
        con, par = cell["connections"], cell["parameters"]
        value = list(con["D"])
        if cell["type"] == "$adffe":
            # Native enable polarity retained exactly; reset dominates enable.
            a, b = (con["Q"], value) if parameter_int(par["EN_POLARITY"]) else (value, con["Q"])
            value = mux(list(a), list(b), con["EN"])
        reset_value = list(par["ARST_VALUE"][::-1])
        value = mux(reset_value, value, con["ARST"])  # active-low checked above
        cached[name] = value
        return value

    ref_next, cand_next = [], []
    for r, c in pairs:
        rn, rc, ri = qdriver[r]
        cn, cc, ci = qdriver[c]
        ref_next.append(effective_next(rn, rc)[ri])
        cand_next.append(effective_next(cn, cc)[ci])
    equal = fresh()
    add("$eq", {"A": ref_next, "B": cand_next, "Y": equal},
        {"A_SIGNED": 0, "B_SIGNED": 0, "A_WIDTH": len(pairs), "B_WIDTH": len(pairs), "Y_WIDTH": 1},
        {"A": "input", "B": "input", "Y": "output"})
    add("$assert", {"A": equal, "EN": ["1"]}, {}, {"A": "input", "EN": "input"})
    removed = []
    for name, cell in list(mod["cells"].items()):
        if cell["type"] not in ("$adff", "$adffe"):
            continue
        q = cell["connections"]["Q"]
        keep = [i for i, bit in enumerate(q) if bit not in alias]
        if len(keep) == len(q):
            continue
        removed.extend(bit for bit in q if bit in alias)
        if not keep:
            del mod["cells"][name]
        else:
            for port in ("Q", "D"):
                cell["connections"][port] = [cell["connections"][port][i] for i in keep]
            rv = cell["parameters"]["ARST_VALUE"][::-1]
            cell["parameters"]["ARST_VALUE"] = "".join(rv[i] for i in keep)[::-1]
            cell["parameters"]["WIDTH"] = format(len(keep), "032b")
    if set(removed) != set(alias):
        raise ValueError("Not every factored candidate FF bit was removed")
    for cell in mod["cells"].values():
        for port, bits in cell["connections"].items():
            cell["connections"][port] = [alias.get(bit, bit) for bit in bits]
    for net in [*mod["netnames"].values(), *mod["ports"].values()]:
        net["bits"] = [alias.get(bit, bit) for bit in net["bits"]]
    return {"factored_state_bits": len(pairs), "pairs": pairs,
            "base": "Exactly one verified initstate -> !native_reset premise; all factored FF reset values match",
            "step": "Assert original effective D/EN/async-reset next-state equality for every factored bit",
            "transition": "Original reference FFs retained, candidate matched Q aliases reference Q",
            "fresh_state_inputs": 0, "assumptions_added": 0,
            "soundness": "Initial-reset base plus first-divergence/inductive state-congruence certificate"}
