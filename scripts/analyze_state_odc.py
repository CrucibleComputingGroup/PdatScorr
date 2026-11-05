#!/usr/bin/env python3
"""Prove generic scalar-control constant ODCs without changing capacities.

The immutable caller-supplied miter owns all assumptions and observations.
Both constants are searched; no safe entry index or occupancy fact is supplied.
Every cumulative trial and the final combined design are checked against the
original. Ordinary downstream synthesis may remove newly unobservable storage.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from odc.state_candidates import scalar_constant_candidates, replace_scalar_constant
from odc.temporal import digest, export_design, prove_pair


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("design", type=Path)
    parser.add_argument("--top", required=True)
    parser.add_argument("--candidate-top", default="StateCandidate")
    parser.add_argument("--harness", type=Path, required=True)
    parser.add_argument("--proof-top", default="TemporalMiter")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--scope", default=".*", help="Regex selecting a source cone, never a safe constant")
    parser.add_argument("--max-probes", type=int, default=32)
    parser.add_argument("--yosys", default="yosys")
    parser.add_argument("--smtbmc", default="yosys-smtbmc")
    parser.add_argument("--solver", default="z3")
    parser.add_argument("--engine", choices=("induction", "pdr"), default="pdr")
    parser.add_argument("--abc", default="abc")
    parser.add_argument("--depth", type=int, default=12)
    parser.add_argument("--timeout", type=float, default=120)
    helpers = parser.add_mutually_exclusive_group()
    helpers.add_argument("--state-helper", dest="state_helper", action="store_true",
                         help="Additionally assert continuing internal-state correspondence")
    helpers.add_argument("--no-state-helper", dest="state_helper", action="store_false",
                         help="Keep initial pairing and functional observations only (default)")
    parser.set_defaults(state_helper=False)
    args = parser.parse_args()
    if args.max_probes < 1 or args.depth < 2 or args.timeout <= 0:
        parser.error("Positive probe/time budgets and proof depth >=2 required")
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    source_files = {"design": args.design.resolve(), "original_harness": args.harness.resolve(),
                    "driver": Path(__file__).resolve(), "candidate_implementation": ROOT / "odc/state_candidates.py",
                    "proof_implementation": ROOT / "odc/temporal.py"}
    source_hashes = {name: digest(path) for name, path in source_files.items()}
    design_bytes = source_files["design"].read_bytes()
    (out / "input.json").write_bytes(design_bytes)
    design = json.loads(design_bytes)
    harness = out / "harness.sv"
    harness.write_bytes(source_files["original_harness"].read_bytes())
    report = {"status": "running", "algorithm": "scalar-output-constant-ODC",
              "design_sha256": source_hashes["design"], "harness_sha256": digest(harness),
              "source_paths": {key: str(path) for key, path in source_files.items()},
              "source_sha256": source_hashes, "top": args.top, "candidate_top": args.candidate_top,
              "scope": args.scope, "max_probes": args.max_probes,
              "assert_state_correspondence": args.state_helper,
              "candidate_types": ["$eq", "$logic_not"], "accepted": [], "probes": []}

    def save() -> None:
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")

    def check_sources() -> None:
        for name, path in source_files.items():
            if digest(path) != source_hashes[name]:
                raise RuntimeError(f"{name} changed during analysis")
        if digest(out / "input.json") != source_hashes["design"]:
            raise RuntimeError("Input snapshot changed during analysis")
        if digest(harness) != source_hashes["original_harness"]:
            raise RuntimeError("Harness snapshot differs from original")

    save()
    try:
        check_sources()
        candidates = scalar_constant_candidates(design, args.top, args.scope)
        report["candidate_count"] = len(candidates)
        reference, identical = out / "reference.v", out / "identical.v"
        export_design(design, args.top, args.top, reference, args.yosys, args.timeout)
        export_design(design, args.top, args.candidate_top, identical, args.yosys, args.timeout)
        kwargs = dict(yosys=args.yosys, smtbmc=args.smtbmc, solver=args.solver,
                      depth=args.depth, timeout=args.timeout, engine=args.engine, abc=args.abc,
                      assert_state_correspondence=args.state_helper)
        report["identity_proof"] = prove_pair(reference, identical, harness, args.proof_top,
                                               out / "identity_proof", **kwargs)
        if not report["identity_proof"]["proven"]:
            report["status"] = "identity_proof_failed"
            save()
            return 1
        current, accepted_cells = design, set()
        for candidate in candidates:
            if candidate["cell"] in accepted_cells:
                continue
            if len(report["probes"]) >= args.max_probes:
                break
            check_sources()
            index = len(report["probes"])
            print(f"Probe {index}: {candidate['cell']} -> {candidate['constant']}", flush=True)
            trial = replace_scalar_constant(current, args.top, candidate)
            variant = out / f"candidate_{index:04d}.v"
            export_design(trial, args.top, args.candidate_top, variant, args.yosys, args.timeout)
            result = prove_pair(reference, variant, harness, args.proof_top,
                                out / f"proof_{index:04d}", **kwargs)
            report["probes"].append({"candidate": candidate, "proof": result})
            if result["proven"]:
                current = trial
                accepted_cells.add(candidate["cell"])
                report["accepted"].append(candidate)
            print("  " + ("PROVED" if result["proven"] else "REJECTED/UNPROVED"), flush=True)
            save()
        final = out / "optimized.v"
        export_design(current, args.top, args.candidate_top, final, args.yosys, args.timeout)
        report["combined_proof"] = prove_pair(reference, final, harness, args.proof_top,
                                              out / "combined_proof", **kwargs)
        check_sources()
        report["optimized_verilog_sha256"] = digest(final)
        report["optimized_json_sha256"] = digest(final.with_suffix(".json"))
        report["search_complete"] = all(c["cell"] in accepted_cells or any(
            p["candidate"] == c for p in report["probes"]) for c in candidates)
        report["status"] = "proved" if report["combined_proof"]["proven"] else "failed"
    except (RuntimeError, OSError, ValueError, KeyError) as error:
        report["status"] = "error"
        report["error"] = str(error)
    save()
    print(f"{report['status']}: {len(report['accepted'])} accepted scalar constants; {out / 'report.json'}")
    return 0 if report["status"] == "proved" else 1


if __name__ == "__main__":
    raise SystemExit(main())
