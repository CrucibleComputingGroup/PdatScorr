"""Generate enabled-register bank sharing candidates, without declaring them safe.

Equal width/reset/clock and exclusive writes are necessary filters, not a
lifetime proof. Every accepted rewrite must separately pass output equivalence
with original consumers. A bank can contain arbitrary values while unobserved.
"""
from __future__ import annotations

import copy
import hashlib
from itertools import combinations
import json
from pathlib import Path
import re

from .temporal import checked_yosys, digest, parameter_int, validate_hardware, yosys_path


def _bits(module):
    return {b for c in module["cells"].values() for bs in c["connections"].values()
            for b in bs if isinstance(b, int)} | {
                b for n in module["netnames"].values() for b in n["bits"] if isinstance(b, int)}


def _signature(cell):
    """Restrict v1 to FFs whose reset dominates enable; no latches/sync-reset CE."""
    if cell["type"] not in ("$dffe", "$adffe"):
        return None
    params, con = cell["parameters"], cell["connections"]
    width = parameter_int(params["WIDTH"])
    if (len(con["Q"]) != width or len(con["D"]) != width
            or len(con["CLK"]) != 1 or len(con["EN"]) != 1):
        raise ValueError("Malformed enabled FF")
    signature = (cell["type"], width, tuple(con["CLK"]), parameter_int(params["CLK_POLARITY"]))
    if cell["type"] == "$adffe":
        signature += (tuple(con["ARST"]), parameter_int(params["ARST_POLARITY"]), params["ARST_VALUE"])
    return signature


def _initial_values(module):
    values = {}
    for net in module["netnames"].values():
        value = net.get("attributes", {}).get("init")
        if value is None:
            continue
        value = format(value, f"0{len(net['bits'])}b") if isinstance(value, int) else value
        if len(value) != len(net["bits"]):
            raise ValueError("Malformed register init attribute")
        for bit, item in zip(net["bits"], reversed(value)):
            if item not in "01":
                continue
            if bit in values and values[bit] != item:
                raise ValueError("Contradictory explicit initial attributes")
            values[bit] = item
    return values


def bank_candidates(design: dict, top: str, *, pattern: str = ".*", min_width: int = 2) -> list[dict]:
    """Enumerate all compatible bank pairs in a regex-scoped cone.

    Scope restricts search cost, not safe state/rows or acceptance. Pairing is
    independent of source field names and never assumes a phase relation.
    """
    validate_hardware(design, top)
    module = design["modules"][top]
    initialized = _initial_values(module)
    match = re.compile(pattern)
    banks = []
    for name, cell in sorted(module["cells"].items()):
        sig = _signature(cell)
        if sig is None or sig[1] < min_width:
            continue
        q = set(cell["connections"]["Q"])
        if len(q) != sig[1] or any(not isinstance(b, int) for b in q):
            raise ValueError("Q bank has constants or repeated bits")
        aliases = [n for n, v in module["netnames"].items() if q.intersection(v["bits"])]
        if not match.search(" ".join([name, cell.get("attributes", {}).get("src", ""), *aliases])):
            continue
        # A merge must not silently combine contradictory explicit init values.
        init = {b: initialized[b] for b in q if b in initialized}
        banks.append((name, cell, sig, aliases, init))
    result = []
    for a, b in combinations(banks, 2):
        if a[2] != b[2]:
            continue
        qa, qb = a[1]["connections"]["Q"], b[1]["connections"]["Q"]
        if set(qa).intersection(qb):
            raise ValueError("Multiply driven register bank")
        if any(a[4].get(x) != b[4].get(y) for x, y in zip(qa, qb)):
            continue
        result.append({"id": f"bank_{len(result):04d}", "keep_cell": a[0], "remove_cell": b[0],
                       "width": a[2][1], "type": a[2][0], "keep_aliases": a[3], "remove_aliases": b[3],
                       "keep_q": qa, "remove_q": qb, "status": "candidate_unproved"})
    return result


def merge_banks(design: dict, top: str, candidate: dict, *, wrong_priority: bool = False) -> dict:
    """Unproved representation rewrite: share Q and union the two write events.

    Writes to the removed bank have priority if both enables assert. The
    exclusivity prefilter and full sequential proof must justify this choice.
    wrong_priority is an explicit negative-control mutation: keep-D on either
    event. It cannot be selected by the candidate generator.
    """
    validate_hardware(design, top)
    result = copy.deepcopy(design)
    mod = result["modules"][top]
    keep, remove = mod["cells"][candidate["keep_cell"]], mod["cells"][candidate["remove_cell"]]
    if _signature(keep) is None or _signature(keep) != _signature(remove):
        raise ValueError("Incompatible bank clocks/reset/width")
    qa, qb = keep["connections"]["Q"], remove["connections"]["Q"]
    if qa != candidate["keep_q"] or qb != candidate["remove_q"]:
        raise ValueError("Stale candidate")
    initialized = _initial_values(mod)
    if any(initialized.get(a) != initialized.get(b) for a, b in zip(qa, qb)):
        raise ValueError("Incompatible explicit initial values")
    prefix = "$pscorr_share_" + candidate["id"]
    if any(n.startswith(prefix) for n in mod["cells"]):
        raise ValueError("Duplicate merge")
    nextbit = max(_bits(mod), default=1) + 1

    def fresh(width=1):
        nonlocal nextbit
        bits = list(range(nextbit, nextbit + width))
        nextbit += width
        return bits

    def add(name, typ, con, params, dirs):
        mod["cells"][prefix + name] = {"hide_name": 1, "type": typ, "parameters": params,
            "attributes": {"pscorr_bank_sharing": candidate["id"]}, "port_directions": dirs,
            "connections": con}

    def active_enable(cell, suffix):
        en = list(cell["connections"]["EN"])
        if not parameter_int(cell["parameters"]["EN_POLARITY"]):
            neg = fresh()
            add(suffix, "$not", {"A": en, "Y": neg},
                {"A_SIGNED": 0, "A_WIDTH": 1, "Y_WIDTH": 1}, {"A": "input", "Y": "output"})
            return neg
        return en

    ea, eb = active_enable(keep, "_ena"), active_enable(remove, "_enb")
    enable, data = fresh(), fresh(len(qa))
    add("_en", "$or", {"A": ea, "B": eb, "Y": enable},
        {"A_SIGNED": 0, "B_SIGNED": 0, "A_WIDTH": 1, "B_WIDTH": 1, "Y_WIDTH": 1},
        {"A": "input", "B": "input", "Y": "output"})
    add("_data", "$mux", {"A": list(keep["connections"]["D"]),
        "B": list(keep["connections"]["D"] if wrong_priority else remove["connections"]["D"]),
        "S": eb, "Y": data}, {"WIDTH": len(qa)}, {"A": "input", "B": "input", "S": "input", "Y": "output"})
    keep["connections"]["D"] = data
    keep["connections"]["EN"] = enable
    keep["parameters"]["EN_POLARITY"] = format(1, "032b")
    del mod["cells"][candidate["remove_cell"]]
    aliases = dict(zip(qb, qa))
    for cell in mod["cells"].values():
        for port, bits in cell["connections"].items():
            cell["connections"][port] = [aliases.get(b, b) for b in bits]
    for net in [*mod["netnames"].values(), *mod["ports"].values()]:
        net["bits"] = [aliases.get(b, b) for b in net["bits"]]
    return result


def filter_exclusive_writes(design: dict, top: str, candidates: list[dict], directory: Path,
                            *, yosys: str, timeout: float = 120) -> dict:
    """Prove CE exclusion for arbitrary prestate; no reachability assumptions.

    Every native FF Q becomes a free input; all ordinary outputs are dropped.
    This stronger combinational check is only a rejection prefilter. It cannot
    certify bank sharing, because mutually exclusive writes can overwrite live
    data. The complete SAT log and common combinational model are retained.
    """
    directory.mkdir(parents=True)
    result = copy.deepcopy(design)
    mod = result["modules"][top]
    mod["ports"] = {n: v for n, v in mod["ports"].items() if v["direction"] == "input"}
    nextbit = max(_bits(mod), default=1) + 1
    for i, (name, cell) in enumerate(list(mod["cells"].items())):
        if cell["type"] in ("$dff", "$adff", "$dffe", "$adffe"):
            q = list(cell["connections"]["Q"])
            mod["ports"][f"state_{i}"] = {"direction": "input", "bits": q}
            del mod["cells"][name]
        elif "ff" in cell["type"].lower() or "latch" in cell["type"].lower() or cell["type"].startswith("$mem"):
            raise ValueError("Unsupported sequential cell in exclusion check")
    for candidate in candidates:
        bits = []
        for side in ("keep_cell", "remove_cell"):
            cell = design["modules"][top]["cells"][candidate[side]]
            en = cell["connections"]["EN"]
            if not parameter_int(cell["parameters"]["EN_POLARITY"]):
                y = [nextbit]
                nextbit += 1
                mod["cells"][f"$invert_{candidate['id']}_{side}"] = {"hide_name": 1, "type": "$not",
                    "parameters": {"A_SIGNED": 0, "A_WIDTH": 1, "Y_WIDTH": 1}, "attributes": {},
                    "port_directions": {"A": "input", "Y": "output"}, "connections": {"A": en, "Y": y}}
                en = y
            bits.append(en)
        out = [nextbit]
        nextbit += 1
        mod["ports"][candidate["id"]] = {"direction": "output", "bits": out}
        mod["cells"]["$overlap_" + candidate["id"]] = {"hide_name": 1, "type": "$and",
            "parameters": {"A_SIGNED": 0, "B_SIGNED": 0, "A_WIDTH": 1, "B_WIDTH": 1, "Y_WIDTH": 1},
            "attributes": {}, "port_directions": {"A": "input", "B": "input", "Y": "output"},
            "connections": {"A": bits[0], "B": bits[1], "Y": out}}
    path = directory / "exclusive.json"
    path.write_text(json.dumps(result) + "\n")
    script = f"read_json {yosys_path(path)}\nhierarchy -check -top {top}\nopt_clean\nbwmuxmap\nbmuxmap\ndemuxmap\nopt_clean\ncheck -assert\n"
    script += "".join(f"sat -prove {c['id']} 0\n" for c in candidates)
    run = checked_yosys(yosys, script, directory, "exclusive", timeout)
    text = Path(run["log"]).read_text()
    outcomes = re.findall(r"Import proof-constraint: \\(bank_\d+) = 1'0.*?SAT proof finished - (?:no model found: (SUCCESS)|model found: (FAIL))!", text, re.S)
    if len(outcomes) != len(candidates):
        raise ValueError("Incomplete SAT exclusion evidence")
    by_id = {cid: bool(success) and not fail for cid, success, fail in outcomes}
    manifest = {"purpose": "Necessary CE-exclusion prefilter, NOT sequential equivalence",
                "hardware_design_sha256": hashlib.sha256(json.dumps(design, sort_keys=True).encode()).hexdigest(),
                "model_sha256": digest(path), "run": run,
                "candidates": [{**c, "exclusive_writes": by_id[c["id"]]} for c in candidates]}
    (directory / "summary.json").write_text(json.dumps(manifest, indent=2) + "\n")
    return manifest
