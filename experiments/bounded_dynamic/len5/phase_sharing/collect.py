#!/usr/bin/env python3
"""Package compact phase-control evidence without converting unknown to success."""
from __future__ import annotations
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    workspace = next(p for p in HERE.parents if (p / "tools/oss-cad-suite-20261104").exists())
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--build", type=Path, default=workspace / "experiments/bounded_dynamic/len5/phase_sharing/build")
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True)
    records = []
    def retain(src, name, compress=False):
        dst = out / name
        dst.parent.mkdir(parents=True, exist_ok=True)
        raw = src.read_bytes()
        dst.write_bytes(gzip.compress(raw, mtime=0) if compress else raw)
        records.append({"path": name, "sha256": digest(dst), "source": str(src.resolve()),
                        "source_sha256": digest(src), "gzip": compress})
    jobs = {
        "full_rob_plain_identity": "proof_v1/identity_proof",
        "alu_cdb_plain_identity": "alu_cdb_proof_v1/identity_proof",
        "native_identity_induction": "alu_cdb_proof_v1/identity_native_induction",
        "native_candidate": "native_candidate_v1/proof",
        "lastwriter_candidate": "native_candidate_v1/lastwriter_proof_v2",
        "factored_identity": "native_candidate_v1/factored_identity",
        "factored_candidate": "native_candidate_v1/factored_lastwriter",
        "coherent_identity": "native_candidate_v1/coherent_identity",
        "coherent_candidate": "native_candidate_v1/coherent_candidate",
        "raw_local_observation_control": "negative_raw_v1/proof",
    }
    outcomes = {}
    for label, rel in jobs.items():
        source = args.build / rel
        proof = json.loads((source / "proof.json").read_text())
        outcomes[label] = {"proven": proof["proven"], "status": "proved" if proof["proven"] else "unknown",
                           "method": proof["method"], "proof_sha256": digest(source / "proof.json")}
        if "pdr" in proof:
            log = (source / "pdr.log").read_text()
            outcomes[label]["seconds"] = proof["pdr"]["seconds"]
            outcomes[label]["counterexample"] = bool(re.search(r"(?m)^Output\s+\d+[^\n]*was asserted", log))
            if outcomes[label]["counterexample"]:
                outcomes[label]["status"] = "counterexample"
        for path in sorted(source.iterdir()):
            if path.suffix in (".ys", ".log", ".py") or path.name == "proof.json":
                retain(path, label + "/" + path.name)
        if label in ("factored_identity", "coherent_candidate"):
            retain(source / "model.aig", label + "/model.aig")
    for label, source in (("baseline_full", "baseline_v3"), ("baseline_component", "alu_cdb_v1")):
        for name in ("manifest.json", "prepare.ys", "prepare.log", "AluObserved.sv"):
            retain(args.build / source / name, label + "/" + name)
    pref = args.build / "alu_cdb_proof_v1/prefilter"
    for name in ("summary.json", "exclusive.ys"):
        retain(pref / name, "prefilter/" + name)
    retain(pref / "exclusive.log", "prefilter/exclusive.log.gz", compress=True)
    for src, name in (
        ("alu_cdb_proof_v1/reference.v", "native/reference.v"),
        ("alu_cdb_proof_v1/BankMiter.sv", "native/BankMiter.sv"),
        ("native_candidate_v1/candidate.v", "native/unaccepted_candidate.v"),
        ("native_candidate_v1/bank_spec.json", "native/bank_spec.json"),
        ("negative_raw_v1/summary.json", "raw_local_observation_control/summary.json"),
        ("native_candidate_v1/lastwriter_proof/failure.json", "setup_failures/lastwriter_metadata.json"),
    ):
        retain(args.build / src, name)
    sat = args.build / "alu_cdb_proof_v1/identity_native_induction/sat_induction"
    for name in ("run.ys", "run.log", "command.json"):
        retain(sat / name, "identity_sat_induction/" + name)
    prefdata = json.loads((pref / "summary.json").read_text())
    final = json.loads((args.build / "native_candidate_v1/coherent_candidate/proof.json").read_text())
    cone = final["coherent_alu_abstraction"]
    shape_a = {r: len(b) for r, b in cone["reference_cone"]["input_bits"].items()}
    shape_b = {r: len(b) for r, b in cone["candidate_cone"]["input_bits"].items()}
    assert shape_a == shape_b == {"ctl_i": 4, "rs1_i": 64, "rs2_i": 64}
    assert len(cone["reference_cone"]["output_bits"]) == len(cone["candidate_cone"]["output_bits"]) == 64
    summary = {
        "status": "no_target_candidate_proven", "accepted_rewrites": 0,
        "purpose": "Program-independent phase-sharing CONTROL, not timing-induced hardware savings",
        "source_commit": "14291dcc5bef181085d001c5a29e7f4fc4cbc8e9",
        "original_capacity": {"ALU_RS": 8}, "baseline_component_ff_bits": 1773,
        "proposed_removed_ff_bits": 64, "physical_mapping_performed": False,
        "candidate_pairs": len(prefdata["candidates"]),
        "exclusive_write_pairs": sum(c["exclusive_writes"] for c in prefdata["candidates"]),
        "results": outcomes,
        "sole_temporal_premise": "Common native reset asserted at initial time; arbitrary later reset/flush/dispatch/operands/CDB contention",
        "consumer_closure": {"path": "../consumer_closure_v3/summary.json",
                             "sha256": digest(HERE / "results/consumer_closure_v3/summary.json"),
                             "scope": "Separate actual-core invalid-global-CDB-payload noninterference lemma"},
        "post_run_guard_audit": {"purpose": "Later per-role-width guard satisfied by the exact archived unknown model",
                                 "reference_inputs": shape_a, "candidate_inputs": shape_b, "output_widths": [64, 64]},
        "interpretation": "Target proofs exhausted short fixed wall budgets; no proof of impossibility or area reduction. Generic small-model positives/negatives are independent regression evidence.",
        "artifacts": records,
    }
    (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({"status": summary["status"], "files": len(records),
                      "bytes": sum(p.stat().st_size for p in out.rglob('*') if p.is_file())}))

if __name__ == "__main__":
    main()
