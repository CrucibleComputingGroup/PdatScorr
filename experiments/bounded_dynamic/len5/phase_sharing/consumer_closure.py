#!/usr/bin/env python3
"""Prove invalid global CDB payload noninterference on the original LEN5 netlist.

The proof cuts global CDB fanout, not RTL behavior. Every register Q is a common
arbitrary prestate input; exact next-state (enable and async reset included) and
every actual core output are compared for two independent CDB payloads.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import copy
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import time


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def pint(value):
    return int(value, 2) if isinstance(value, str) else value


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def run(yosys, directory, name, script):
    ys, log = directory / (name + ".ys"), directory / (name + ".log")
    ys.write_text(script)
    start = time.monotonic()
    with log.open("w") as out:
        result = subprocess.run([str(yosys), "-Q", "-T", "-s", str(ys)],
                                stdout=out, stderr=subprocess.STDOUT, timeout=180)
    record = {"returncode": result.returncode, "seconds": time.monotonic() - start,
              "script_sha256": sha(ys), "log_sha256": sha(log)}
    if result.returncode:
        raise RuntimeError(f"Yosys failed; see {log}")
    return record


def main():
    here = Path(__file__).resolve().parent
    workspace = next(p for p in here.parents if (p / "tools/oss-cad-suite-20261104").exists())
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--frontend", type=Path, default=workspace / "experiments/bounded_dynamic/len5/build/pre_fpu_frontend")
    parser.add_argument("--build", type=Path, default=workspace / "experiments/bounded_dynamic/len5/build/consumer_closure_v3")
    parser.add_argument("--evidence", type=Path, default=here / "results/consumer_closure_v3")
    args = parser.parse_args()
    args.build.mkdir(parents=True, exist_ok=False)
    args.evidence.mkdir(parents=True, exist_ok=False)
    yosys = workspace / "tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys"
    manifest = json.loads((args.frontend / "manifest.json").read_text())
    assert manifest["upstream_commit"] == "14291dcc5bef181085d001c5a29e7f4fc4cbc8e9"
    assert not manifest["baseline_switches"] and not manifest["compatibility_edits"]
    assert manifest["original_sha256"] == manifest["prepared_sha256"]
    assert sha(args.frontend / "normalized.il") == manifest["normalized_il_sha256"]
    for path, expected in manifest["prepared_sha256"].items():
        assert sha(args.frontend / "source" / path) == expected, path
    model = args.build / "consumer_original.json"
    preparation = run(yosys, args.build, "prepare", f'''read_rtlil "{args.frontend / 'normalized.il'}"
hierarchy -check -top datapath
select -assert-none t:$assert t:$assume t:$check
select *
bwmuxmap
bmuxmap
demuxmap
memory_map
setundef -anyseq
opt -keepdc
check -assert
write_json "{model}"
''')
    design = json.loads(model.read_text())
    mod = design["modules"]["datapath"]
    original_outputs = [n for n, p in mod["ports"].items() if p["direction"] == "output"]
    data = mod["netnames"]["u_backend.cdb_others_data"]["bits"]
    valid = mod["netnames"]["u_backend.cdb_others_valid"]["bits"]
    assert len(data) == 75 and len(set(data)) == 75 and all(isinstance(b, int) for b in data)
    assert len(valid) == 1 and isinstance(valid[0], int)
    maxbit = max(b for n in mod["netnames"].values() for b in n["bits"] if isinstance(b, int))
    serial = 0

    def fresh(width=1):
        nonlocal maxbit
        bits = list(range(maxbit + 1, maxbit + width + 1))
        maxbit += width
        return bits

    def add(typ, con, params, dirs):
        nonlocal serial
        name = "$closure_" + str(serial)
        serial += 1
        mod["cells"][name] = {"hide_name": 1, "type": typ, "parameters": params,
                              "attributes": {}, "port_directions": dirs, "connections": con}

    def active(bits, polarity):
        if pint(polarity):
            return bits
        out = fresh()
        add("$not", {"A": bits, "Y": out}, {"A_SIGNED": 0, "A_WIDTH": 1, "Y_WIDTH": 1},
            {"A": "input", "Y": "output"})
        return out

    def mux(a, b, s):
        assert len(a) == len(b)
        out = fresh(len(a))
        add("$mux", {"A": a, "B": b, "S": s, "Y": out}, {"WIDTH": len(a)},
            {"A": "input", "B": "input", "S": "input", "Y": "output"})
        return out

    # Override only consumers; the original producer remains intact. No original
    # output port aliases this boundary. No capacity/state interpretation is used.
    new_data, new_valid = fresh(75), fresh()
    remap = dict(zip(data + valid, new_data + new_valid))
    consumers = []
    for name, cell in mod["cells"].items():
        for port, bits in cell["connections"].items():
            if cell["port_directions"][port] != "input":
                continue
            if any(b in remap for b in bits):
                consumers.append({"cell": name, "port": port, "source": cell.get("attributes", {}).get("src", "")})
                cell["connections"][port] = [remap.get(b, b) for b in bits]
    for name in original_outputs:
        assert not set(mod["ports"][name]["bits"]).intersection(remap), name
    mod["ports"]["cdb_payload"] = {"direction": "input", "bits": new_data}
    mod["ports"]["cdb_valid"] = {"direction": "input", "bits": new_valid}

    ffs, arbitrary, q_seen = [], [], set()
    for index, (name, cell) in enumerate(list(mod["cells"].items())):
        typ, con, par = cell["type"], cell["connections"], cell["parameters"]
        if typ == "$anyseq":
            mod["ports"][f"undefined_{index}"] = {"direction": "input", "bits": con["Y"]}
            arbitrary.append({"cell": name, "width": len(con["Y"])})
            del mod["cells"][name]
        elif typ in ("$dff", "$dffe", "$adff", "$adffe"):
            q, d = con["Q"], con["D"]
            assert all(isinstance(b, int) for b in q) and len(set(q)) == len(q)
            assert not q_seen.intersection(q), "Multiple FF drivers"
            q_seen.update(q)
            # All native registers share the single positive-edge clock. No
            # clock gating or mixed edge abstraction is silently introduced.
            assert pint(par["CLK_POLARITY"]) == 1 and con["CLK"] == mod["ports"]["clk_i"]["bits"]
            if "EN" in con:
                d = mux(q, d, active(con["EN"], par["EN_POLARITY"]))
            if "ARST" in con:
                reset = list(reversed(par["ARST_VALUE"]))
                assert set(reset) <= {"0", "1"}
                d = mux(d, reset, active(con["ARST"], par["ARST_POLARITY"]))
            mod["ports"][f"state_{index}"] = {"direction": "input", "bits": q}
            mod["ports"][f"next_{index}"] = {"direction": "output", "bits": d}
            ffs.append({"cell": name, "type": typ, "width": len(q), "state_port": f"state_{index}", "next_port": f"next_{index}"})
            del mod["cells"][name]
        elif "ff" in typ.lower() or "latch" in typ.lower() or typ.startswith("$mem"):
            raise ValueError(f"Unsupported sequential cell {name}: {typ}")
    for net in mod["netnames"].values():
        net.get("attributes", {}).pop("init", None)
    mod["attributes"].pop("top", None)

    # Common arbitrary Q and ordinary inputs, independent 75-bit CDB payloads.
    top = {"attributes": {"top": 1}, "ports": {}, "cells": {}, "netnames": {}}
    count = 1
    def allocate(n):
        nonlocal count
        bits = list(range(count + 1, count + n + 1)); count += n
        return bits
    connections = [{}, {}]
    compared = [[], []]
    for name, port in mod["ports"].items():
        width = len(port["bits"])
        if port["direction"] == "input" and name != "cdb_payload":
            bits = allocate(width)
            top["ports"][name] = {"direction": "input", "bits": bits}
            for conn in connections:
                conn[name] = bits
        else:
            for side, conn in enumerate(connections):
                bits = allocate(width); conn[name] = bits
                if port["direction"] == "input":
                    top["ports"][f"cdb_payload_{side}"] = {"direction": "input", "bits": bits}
                else:
                    compared[side].extend(bits)
    for side, conn in enumerate(connections):
        top["cells"][f"copy{side}"] = {"hide_name": 0, "type": "ConsumerStep", "parameters": {}, "attributes": {},
            "port_directions": {n: p["direction"] for n, p in mod["ports"].items()}, "connections": conn}
    equal = allocate(1)
    top["ports"]["equal"] = {"direction": "output", "bits": equal}
    top["cells"]["compare"] = {"hide_name": 0, "type": "$eq", "parameters": {"A_SIGNED": 0, "B_SIGNED": 0,
        "A_WIDTH": len(compared[0]), "B_WIDTH": len(compared[1]), "Y_WIDTH": 1}, "attributes": {},
        "port_directions": {"A": "input", "B": "input", "Y": "output"},
        "connections": {"A": compared[0], "B": compared[1], "Y": equal}}
    miter = args.build / "consumer_miter.json"
    write(miter, {"modules": {"ConsumerStep": mod, "ConsumerClosure": top}})
    write(args.build / "cut_audit.json", {"registers": ffs, "undefined_inputs": arbitrary, "boundary_consumers": consumers})
    invalid_model = args.build / "invalid_model.json"
    valid_model = args.build / "valid_model.json"
    specialization = run(yosys, args.build, "specialize", f'''read_json "{miter}"
hierarchy -check -top ConsumerClosure
flatten
check -assert
select -assert-none t:$dff t:$dffe t:$adff t:$adffe t:$anyseq t:$assert t:$assume
select *
design -save unrestricted
delete -input w:cdb_valid
connect -nounset -set cdb_valid 1'0
opt -keepdc
check -assert
write_json "{invalid_model}"
design -load unrestricted
delete -input w:cdb_valid
connect -nounset -set cdb_valid 1'1
opt -keepdc
check -assert
write_json "{valid_model}"
''')
    # Replacing an internal combinational driver with a fresh unconstrained
    # input is an overapproximation: every original valuation is retained.
    # Ordinary merging has made this multiplier a shared node in the miter.
    # Its arbitrary output avoids irrelevant nonlinear arithmetic in the SAT
    # database; no multiplier fact or behavior is assumed by the proof.
    invalid = json.loads(invalid_model.read_text())
    im = invalid["modules"]["ConsumerClosure"]
    abstractions = []
    for name, cell in list(im["cells"].items()):
        if cell["type"] == "$mul":
            assert cell["port_directions"]["Y"] == "output"
            im["ports"][f"abstract_mul_{len(abstractions)}"] = {"direction": "input", "bits": cell["connections"]["Y"]}
            abstractions.append({"cell": name, "original_cell": cell})
            del im["cells"][name]
    assert len(abstractions) == 1
    eqs = [(n, c) for n, c in im["cells"].items() if c["connections"].get("Y") == im["ports"]["equal"]["bits"]]
    assert len(eqs) == 1 and eqs[0][1]["type"] == "$eq"
    eq_name, eq_cell = eqs[0]
    remaining = len(eq_cell["connections"]["A"])
    assert remaining == len(eq_cell["connections"]["B"])
    abstract_path = args.build / "invalid_abstract.json"
    write(abstract_path, invalid)
    write(args.build / "arithmetic_abstraction.json", abstractions)

    def partition(start):
        stop = min(start + 64, remaining)
        piece = copy.deepcopy(invalid)
        cmp = piece["modules"]["ConsumerClosure"]["cells"][eq_name]
        for port in ("A", "B"):
            cmp["connections"][port] = cmp["connections"][port][start:stop]
            cmp["parameters"][port + "_WIDTH"] = stop - start
        name = f"partition_{start:05d}"
        path = args.build / (name + ".json")
        write(path, piece)
        record = run(yosys, args.build, name, f'''read_json "{path}"
hierarchy -check -top ConsumerClosure
opt_clean
check -assert
sat -verify -prove equal 1
''')
        assert (args.build / (name + ".log")).read_text().count("no model found: SUCCESS!") == 1
        print(f"proved comparison bits [{start},{stop})", flush=True)
        return {"start": start, "stop": stop, "model_sha256": sha(path), **record}

    with ThreadPoolExecutor(max_workers=2) as pool:
        partitions = list(pool.map(partition, range(0, remaining, 64)))
    assert partitions[0]["start"] == 0 and partitions[-1]["stop"] == remaining
    assert all(a["stop"] == b["start"] for a, b in zip(partitions, partitions[1:]))
    negative = run(yosys, args.build, "negative", f'''read_json "{valid_model}"
hierarchy -check -top ConsumerClosure
opt_clean
check -assert
sat -prove equal 1 -show cdb_payload_0 -show cdb_payload_1 -dump_json "{args.build / 'valid_counterexample.json'}"
''')
    assert (args.build / "negative.log").read_text().count("model found: FAIL!") == 1
    summary = {"scope": "Actual original whole-core netlist one-step CDB consumer noninterference; not a bank-sharing or full-core candidate-equivalence proof",
        "status": "proved_invalid_payload_irrelevant", "source_commit": manifest["upstream_commit"],
        "frontend_manifest_sha256": sha(args.frontend / "manifest.json"), "normalized_il_sha256": sha(args.frontend / "normalized.il"),
        "all_original_source_hashes_verified": True, "capacities": manifest["capacity_parameters_unchanged"],
        "model_sha256": sha(model), "miter_sha256": sha(miter), "cut_audit_sha256": sha(args.build / "cut_audit.json"),
        "script_sha256": sha(__file__), "yosys_sha256": sha(yosys), "preparation": preparation, "specialization": specialization,
        "invalid_model_sha256": sha(invalid_model), "valid_model_sha256": sha(valid_model),
        "invalid_abstract_sha256": sha(abstract_path), "arithmetic_abstraction_sha256": sha(args.build / "arithmetic_abstraction.json"),
        "partitioned_nontrivial_comparison_bits": remaining, "partitions": partitions, "negative_run": negative,
        "arithmetic_abstraction": "One shared 128-bit multiplier driver replaced by arbitrary common input: a stronger overapproximated proof query, never a hardware rewrite.",
        "compared_original_output_ports": original_outputs, "compared_bits": len(compared[0]),
        "arbitrary_common_prestate_bits": sum(f["width"] for f in ffs), "state_banks": len(ffs),
        "symbolic_common_undefined_bits": sum(a["width"] for a in arbitrary),
        "independent_cdb_payload_bits_per_copy": 75,
        "positive_query": "For every common arbitrary prestate, reset/enable and ordinary inputs, cdb_valid=0 implies all original core outputs and exact native next-state are equal for two independent CDB payloads.",
        "negative_control": "At cdb_valid=1, payload changes can affect observations; SAT witness retained.",
        "reset_domain": "No reset or reachability assumption. Async reset values dominate enable in exact next-state expansion; common clock polarity asserted.",
        "limitations": "Boundary consumer substitution lemma only. Producer validity/payload equivalence and transformed storage relation must be proved separately. Undefined source values remain symbolic and common across the comparison."}
    write(args.build / "summary.json", summary)
    names = ["summary.json", "cut_audit.json", "arithmetic_abstraction.json", "prepare.ys", "prepare.log", "specialize.ys", "specialize.log", "negative.ys", "negative.log", "valid_counterexample.json"]
    names += [p.name for pattern in ("partition_*.ys", "partition_*.log") for p in args.build.glob(pattern)]
    for name in names:
        shutil.copy2(args.build / name, args.evidence / name)
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
