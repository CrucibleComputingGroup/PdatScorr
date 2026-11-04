#!/usr/bin/env python3
"""Discover and prove timing-dependent comparator ODCs on fixed elaborated RTL.

The supplied immutable miter instantiates the original top and --candidate-top,
shares inputs, enforces external timing assumptions, and asserts all observations.
Every accepted cumulative mutation is checked against the ORIGINAL design.
"""
import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from odc.temporal import (digest, equality_candidates, export_design,
                          narrow_equality, prove_pair)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("design", type=Path)
    parser.add_argument("--top", required=True)
    parser.add_argument("--candidate-top", default="MshrCandidate")
    parser.add_argument("--harness", type=Path, required=True)
    parser.add_argument("--proof-top", default="TemporalMiter")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--scope", default=".*", help="Regex selecting candidate source cone")
    parser.add_argument("--yosys", default="yosys")
    parser.add_argument("--smtbmc", default="yosys-smtbmc")
    parser.add_argument("--solver", default="z3")
    parser.add_argument("--engine", choices=("induction", "pdr"), default="induction")
    parser.add_argument("--abc", default="abc")
    parser.add_argument("--depth", type=int, default=12)
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("--max-probes", type=int, default=100)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    implementation = Path(__file__).resolve().parents[1] / "odc/temporal.py"
    (out / "temporal_source.py").write_bytes(implementation.read_bytes())
    (out / "driver_source.py").write_bytes(Path(__file__).read_bytes())
    design = json.loads(args.design.read_text())
    harness = out / "harness.sv"
    harness.write_bytes(args.harness.read_bytes())
    reference = out / "reference.v"
    export_design(design, args.top, args.top, reference, args.yosys, args.timeout)
    candidates = equality_candidates(design, args.top, args.scope)
    current = design
    accepted_cells = set()
    report = {"status": "running", "design_sha256": digest(args.design),
              "harness_sha256": digest(harness), "top": args.top,
              "scope": args.scope, "candidate_count": len(candidates),
              "accepted": [], "probes": []}
    kwargs = dict(yosys=args.yosys, smtbmc=args.smtbmc, solver=args.solver,
                  depth=args.depth, timeout=args.timeout, engine=args.engine, abc=args.abc)
    # Sanity-check the harness on two identical exports before mutation.
    identical = out / "identical.v"
    export_design(design, args.top, args.candidate_top, identical, args.yosys, args.timeout)
    report["identity_proof"] = prove_pair(reference, identical, harness, args.proof_top,
                                           out / "identity_proof", **kwargs)
    if not report["identity_proof"]["proven"]:
        report["status"] = "identity_proof_failed"
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
        return 1
    for candidate in candidates:
        if candidate["cell"] in accepted_cells:
            continue
        if len(report["probes"]) >= args.max_probes:
            break
        index = len(report["probes"])
        print(f"Probe {index}: {candidate['cell']} -> {candidate['retained_low_bits']} bits", flush=True)
        trial = narrow_equality(current, args.top, candidate)
        variant = out / f"candidate_{index:04d}.v"
        export_design(trial, args.top, args.candidate_top, variant, args.yosys, args.timeout)
        proof = prove_pair(reference, variant, harness, args.proof_top,
                           out / f"proof_{index:04d}", **kwargs)
        probe = {"candidate": candidate, "proof": proof}
        report["probes"].append(probe)
        if proof["proven"]:
            current = trial
            accepted_cells.add(candidate["cell"])
            report["accepted"].append(candidate)
        print("  " + ("PROVED" if proof["proven"] else "REJECTED/UNPROVED"), flush=True)
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    final = out / "optimized.v"
    export_design(current, args.top, args.candidate_top, final, args.yosys, args.timeout)
    report["combined_proof"] = prove_pair(reference, final, harness, args.proof_top,
                                            out / "combined_proof", **kwargs)
    report["status"] = "proved" if report["combined_proof"]["proven"] else "failed"
    report["optimized_verilog_sha256"] = digest(final)
    report["optimized_json_sha256"] = digest(final.with_suffix(".json"))
    report["search_complete"] = all(c["cell"] in accepted_cells or any(
        p["candidate"] == c for p in report["probes"]) for c in candidates)
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"{report['status']}: {len(report['accepted'])} accepted equalities; {out / 'report.json'}")
    return 0 if report["status"] == "proved" else 1


if __name__ == "__main__":
    raise SystemExit(main())
