#!/usr/bin/env python3
"""Audit and copy compact evidence; never turn an incomplete run into a result."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--analysis", type=Path, required=True)
    parser.add_argument("--physical", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    base, analysis, physical = [p.resolve() for p in (args.baseline, args.analysis, args.physical)]
    report = json.loads((analysis / "report.json").read_text())
    mapping = json.loads((physical / "summary.json").read_text())
    original = json.loads((base / "baseline.json").read_text())["modules"]["MshrObserved"]
    optimized = json.loads((analysis / "optimized.json").read_text())["modules"]["MshrObserved"]
    assert report["status"] == "proved" and report["combined_proof"]["proven"]
    assert report["design_sha256"] == sha(base / "baseline.json")
    assert original["ports"] == optimized["ports"] and original["netnames"] == optimized["netnames"]
    assert set(original["cells"]) == set(optimized["cells"])
    changed = [name for name in original["cells"] if original["cells"][name] != optimized["cells"][name]]
    assert set(changed) == {c["cell"] for c in report["accepted"]}
    assert len(changed) == 2
    for name in changed:
        before, after = original["cells"][name], optimized["cells"][name]
        assert before["type"] == after["type"] == "$eq"
        assert before["connections"]["Y"] == after["connections"]["Y"]
        for port in ("A", "B"):
            assert len(before["connections"][port]) == 2 and after["connections"][port] == before["connections"][port][:1]
    for name, filename in (("baseline", "reference.v"), ("optimized", "optimized.v")):
        assert mapping["variants"][name]["source_sha256"] == sha(analysis / filename)
    assert mapping["analysis_report_sha256"] == sha(analysis / "report.json")
    proof_dirs = [analysis / "identity_proof", analysis / "combined_proof"]
    proof_dirs += sorted(analysis.glob("proof_[0-9]*"))
    for directory in proof_dirs:
        proof = json.loads((directory / "proof.json").read_text())
        assert proof["proven"] and proof["pdr"]["returncode"] == 0 and not proof["pdr"]["timeout"]
        assert proof["pdr"]["log_sha256"] == sha(directory / "pdr.log")
        assert "constant undef bits with constant zero" not in (directory / "aig_export.log").read_text()
        assert proof["implementation_sha256"] == sha(analysis / "temporal_source.py")
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    artifacts = {}
    def copy(source, relative):
        target = out / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        artifacts[str(relative)] = {"sha256": sha(target), "source": str(source), "bytes": target.stat().st_size}
    for filename in ("manifest.json", "baseline.json", "MshrObserved.sv", "baseline.ys"):
        copy(base / filename, Path("baseline") / filename)
    for filename in ("report.json", "harness.sv", "reference.v", "optimized.v", "optimized.json", "temporal_source.py"):
        copy(analysis / filename, Path("automatic") / filename)
    for directory in proof_dirs:
        for filename in ("proof.json", "pdr.log", "prepare.ys", "aig_export.ys", "aig_export.log"):
            copy(directory / filename, Path("automatic") / directory.name / filename)
    copy(physical / "summary.json", Path("physical/summary.json"))
    for variant in ("baseline", "optimized"):
        for filename in ("stat.json", "map.ys", "map.log"):
            copy(physical / variant / filename, Path("physical") / variant / filename)
    ff = {name: sum(count for cell, count in data["cell_types"].items()
                   if cell.startswith(("sky130_fd_sc_hd__df", "sky130_fd_sc_hd__edf")))
          for name, data in mapping["variants"].items()}
    summary = {"status": "audited", "scope": "Original RSD component at fixed capacities; not a full-core area or application claim",
        "changed_cells": changed, "mutation": "Automatically reduce each of two equality cells from two bits to its low bit",
        "all_other_cells_ports_and_netnames_unchanged": True,
        "physical_area": {name: data["cell_area"] for name, data in mapping["variants"].items()},
        "physical_area_reduction_percent": mapping["area_reduction_percent"], "physical_flipflops": ff,
        "artifacts": artifacts}
    (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({key: value for key, value in summary.items() if key != "artifacts"}, indent=2))


if __name__ == "__main__":
    main()
