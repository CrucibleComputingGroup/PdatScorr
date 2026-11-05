"""Proof-only last-writer certificates derived from actual enabled FF pairs.

The monitor and representation equalities are proof state/assertions. No
representation premise is assumed, and no monitor enters the mapped hardware.
"""
from __future__ import annotations
from odc.temporal import parameter_int


def add_last_writer_assertion(miter, top, original, original_top, bank):
    mod = miter["modules"][top]
    source = original["modules"][original_top]
    native_q = {b for c in mod["cells"].values() if c["type"] in ("$adff", "$adffe")
                for b in c["connections"]["Q"]}

    def bind(bits, instance):
        resolved = []
        for bit in bits:
            found = set()
            for name, net in source["netnames"].items():
                target = mod["netnames"].get(instance + "." + name)
                if target is None or len(target["bits"]) != len(net["bits"]):
                    continue
                for i, b in enumerate(net["bits"]):
                    if b == bit and target["bits"][i] in native_q:
                        found.add(target["bits"][i])
            if len(found) != 1:
                raise ValueError("Cannot bind one unique native FF Q for bank bit")
            resolved.append(found.pop())
        return resolved

    qa = bind(bank["keep_q"], "reference")
    qb = bind(bank["remove_q"], "reference")
    shared = bind(bank["keep_q"], "candidate")
    if shared != bind(bank["remove_q"], "candidate"):
        raise ValueError("Candidate Q aliases do not implement expected sharing")

    def driver(q):
        found = [c for c in mod["cells"].values() if c["type"] == "$adffe" and c["connections"]["Q"] == q]
        if len(found) != 1:
            raise ValueError("Expected one native enabled bank after opt_dff")
        return found[0]

    a, b = driver(qa), driver(qb)
    for port in ("CLK", "ARST"):
        if a["connections"][port] != b["connections"][port]:
            raise ValueError("Monitor banks have incompatible clocks/reset")
    for param in ("CLK_POLARITY", "ARST_POLARITY", "ARST_VALUE"):
        if a["parameters"][param] != b["parameters"][param]:
            raise ValueError("Monitor banks have incompatible reset values")
    nextbit = max(b for c in mod["cells"].values() for bs in c["connections"].values()
                  for b in bs if isinstance(b, int)) + 1
    prefix = "$pscorr_last_writer_" + bank["id"]
    if any(n.startswith(prefix) for n in mod["cells"]):
        raise ValueError("Duplicate last-writer monitor")

    def fresh(width=1):
        nonlocal nextbit
        bits = list(range(nextbit, nextbit + width))
        nextbit += width
        return bits

    def cell(suffix, kind, ports, params, dirs):
        mod["cells"][prefix + suffix] = {"hide_name": 1, "type": kind, "parameters": params,
            "attributes": {"pscorr_proof_only": 1}, "port_directions": dirs, "connections": ports}

    def active(ff, name):
        en = ff["connections"]["EN"]
        if parameter_int(ff["parameters"]["EN_POLARITY"]):
            return en
        y = fresh()
        cell(name, "$not", {"A": en, "Y": y}, {"A_SIGNED": 0, "A_WIDTH": 1, "Y_WIDTH": 1},
             {"A": "input", "Y": "output"})
        return y

    ea, eb = active(a, "_ena"), active(b, "_enb")
    last, clear_a, next_last, expected, equal = fresh(), fresh(), fresh(), fresh(len(qa)), fresh()
    cell("_clear_a", "$mux", {"A": last, "B": ["0"], "S": ea, "Y": clear_a}, {"WIDTH": 1},
         {"A": "input", "B": "input", "S": "input", "Y": "output"})
    cell("_set_b", "$mux", {"A": clear_a, "B": ["1"], "S": eb, "Y": next_last}, {"WIDTH": 1},
         {"A": "input", "B": "input", "S": "input", "Y": "output"})
    cell("_flag", "$adff", {"CLK": a["connections"]["CLK"], "ARST": a["connections"]["ARST"],
         "D": next_last, "Q": last}, {"WIDTH": 1, "CLK_POLARITY": a["parameters"]["CLK_POLARITY"],
         "ARST_POLARITY": a["parameters"]["ARST_POLARITY"], "ARST_VALUE": "0"},
         {"CLK": "input", "ARST": "input", "D": "input", "Q": "output"})
    cell("_expected", "$mux", {"A": qa, "B": qb, "S": last, "Y": expected}, {"WIDTH": len(qa)},
         {"A": "input", "B": "input", "S": "input", "Y": "output"})
    cell("_equal", "$eq", {"A": shared, "B": expected, "Y": equal},
         {"A_SIGNED": 0, "B_SIGNED": 0, "A_WIDTH": len(qa), "B_WIDTH": len(qa), "Y_WIDTH": 1},
         {"A": "input", "B": "input", "Y": "output"})
    cell("_assert", "$assert", {"A": equal, "EN": ["1"]}, {}, {"A": "input", "EN": "input"})
    return {"candidate_id": bank["id"], "width": len(qa), "reference_a_q": qa,
            "reference_b_q": qb, "candidate_shared_q": shared,
            "reference_a_enable": ea, "reference_b_enable": eb, "last_writer_q": last,
            "assertion": "shared Q == (last writer was B ? original B Q : original A Q)",
            "assumptions_added": 0, "hardware_modified": False,
            "reset_last_writer": "A; the two native banks have identical async reset values"}
