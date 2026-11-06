#!/usr/bin/env python3
"""Apply certified flip-flop constants to the fixed-capacity core netlist.

Every consumer of a certified constant Q net (each cell input port bit and each
module output port bit) is rewired to the proved binary value. The flip-flop
itself, the RTL capacities, and all other connectivity are unchanged; synthesis
then removes state and logic that no longer reaches an observable output.

With several constants files, only bits certified constant with the same value
in every file are applied (the constants common to all of those platforms).

With --simulation-bound, the input is instead one timing_witness.py bound: bits
not yet witnessed varying, which are not certified. The output is then marked as
an uncertified bound; it serves only as an optimistic area bound, never as an
optimized design.
"""
from __future__ import annotations

import argparse
import collections
import copy
import json
from pathlib import Path
import shutil
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
sys.path.insert(0, str(REPO))
from odc.temporal import digest  # noqa: E402

FF_TYPES = {"$aldff", "$adff", "$dffe", "$dff"}


BOUND_STATUS = "simulation_bound_not_certified"


def load_constants(paths: list[Path], design_sha: str, bound: bool = False) -> tuple[dict, list[dict]]:
    if bound and len(paths) != 1:
        raise ValueError("A simulation bound is applied alone")
    sets, sources = [], []
    for path in paths:
        data = json.loads(path.read_text())
        if data.get("status") != (BOUND_STATUS if bound else "certified") or data.get("design_sha256") != design_sha:
            raise ValueError(f"{path} is not a {'simulation bound' if bound else 'certified constant set'} "
                             "for this design")
        if bound and data.get("witness_status") != "passed":
            raise ValueError(f"{path} does not come from a passed witness run")
        sets.append({(c["cell"], c["bit"]): c for c in data["constants"]})
        sources.append({"path": str(path.resolve()), "sha256": digest(path), "gap": data.get("gap"),
                        "model_aig_sha256": data.get("model_aig_sha256"), "constant_bits": len(data["constants"])})
    common = {}
    for key, entry in sets[0].items():
        if all(key in s and s[key]["value"] == entry["value"] and s[key]["net"] == entry["net"] for s in sets[1:]):
            common[key] = entry
    return common, sources


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--design", type=Path, required=True)
    ap.add_argument("--constants", type=Path, nargs="+", required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--simulation-bound", action="store_true",
                    help="Apply one uncertified timing_witness.py bound, for an optimistic area bound only")
    args = ap.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    shutil.copyfile(Path(__file__), out / "substitute.py")
    design_sha = digest(args.design)
    design = json.loads(args.design.read_text())
    if set(design["modules"]) != {"datapath"}:
        raise ValueError("Expected one flattened datapath module")
    constants, sources = load_constants(args.constants, design_sha, args.simulation_bound)
    module = design["modules"]["datapath"]
    net_value = {}
    for (cell_name, bit), entry in constants.items():
        cell = module["cells"].get(cell_name)
        if cell is None or cell["type"] not in FF_TYPES or cell["connections"]["Q"][bit] != entry["net"]:
            raise ValueError(f"Constant {cell_name}[{bit}] does not name a flip-flop Q bit of this design")
        if cell["type"] == "$aldff" and cell["connections"]["AD"][bit] != str(entry["value"]):
            raise ValueError(f"Constant {cell_name}[{bit}] differs from its reset value")
        if cell["type"] not in ("$aldff", "$adff"):
            raise ValueError(f"Constant {cell_name}[{bit}] has no reset value")
        net_value[entry["net"]] = str(entry["value"])
    result = copy.deepcopy(design)
    rmodule = result["modules"]["datapath"]
    rewired = collections.Counter()
    for name, cell in rmodule["cells"].items():
        directions = cell.get("port_directions")
        if directions is None:
            raise ValueError(f"Cell {name} lacks port directions")
        for port, bits in cell["connections"].items():
            if directions[port] == "output":
                continue
            if directions[port] != "input":
                raise ValueError(f"Unsupported port direction on {name}.{port}")
            new = [net_value.get(b, b) if isinstance(b, int) else b for b in bits]
            changed = sum(a != b for a, b in zip(bits, new))
            if changed:
                cell["connections"][port] = new
                rewired[f"{cell['type']}.{port}"] += changed
    for name, port in rmodule["ports"].items():
        if port["direction"] == "output":
            new = [net_value.get(b, b) if isinstance(b, int) else b for b in port["bits"]]
            changed = sum(a != b for a, b in zip(port["bits"], new))
            if changed:
                # The port wire is also listed as a net name; both must name the same bits,
                # otherwise the importer connects the port wire to the constant and the net.
                netname = rmodule["netnames"].get(name)
                if netname is None or netname["bits"] != port["bits"]:
                    raise ValueError(f"Output port {name} has no matching net name entry")
                port["bits"] = new
                netname["bits"] = list(new)
                rewired[f"module_output.{name}"] += changed
    # No consumer of a constant net may remain.
    for name, cell in rmodule["cells"].items():
        for port, bits in cell["connections"].items():
            if cell["port_directions"][port] == "input" and any(b in net_value for b in bits if isinstance(b, int)):
                raise AssertionError(f"Residual consumer {name}.{port}")
    sensitive = {k: v for k, v in rewired.items()
                 if k.split(".")[-1] in ("CLK", "ALOAD", "ARST", "AD", "SET", "CLR")}
    if sensitive:
        raise ValueError(f"Constants reach clock/reset/load controls: {sensitive}")
    (out / "design.json").write_text(json.dumps(result) + "\n")
    (out / "applied_constants.json").write_text(json.dumps(
        [{"cell": k[0], "bit": k[1], "net": v["net"], "value": v["value"]} for k, v in sorted(constants.items())]) + "\n")
    record = {"status": "substituted_simulation_bound" if args.simulation_bound else "substituted", "design": str(args.design.resolve()), "design_sha256": design_sha,
              "constant_sources": sources, "applied_constant_bits": len(constants),
              "applied_zero_bits": sum(v == "0" for v in net_value.values()),
              "applied_one_bits": sum(v == "1" for v in net_value.values()),
              "rewired_connections": dict(sorted(rewired.items())),
              "output_design_sha256": digest(out / "design.json"),
              "applied_constants_sha256": digest(out / "applied_constants.json"),
              "script_sha256": digest(Path(__file__))}
    (out / "summary.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({k: record[k] for k in ("status", "applied_constant_bits", "rewired_connections")}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
