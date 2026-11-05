#!/usr/bin/env python3
"""Enumerate, prefilter and proof-check generic LEN5 phase-sharing candidates."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
sys.path.insert(0, str(REPO))
from odc.bank_sharing import bank_candidates, filter_exclusive_writes, merge_banks
from odc.temporal import digest, export_design, prove_pair


def miter_text(module, *, reference="AluReference", candidate="AluCandidate"):
    lines = ["// Shared external inputs; only an initial reset is assumed.", "module BankMiter("]
    inputs = {n: p for n, p in module["ports"].items() if p["direction"] == "input"}
    outputs = {n: p for n, p in module["ports"].items() if p["direction"] == "output"}
    for n, p in inputs.items():
        lines.append(f"  input wire [{len(p['bits'])-1}:0] {n},")
    lines[-1] = lines[-1].removesuffix(",")
    lines += [");", "  always @* if ($initstate) assume (!rst_ni);"]
    for n, p in outputs.items():
        lines.append(f"  wire [{len(p['bits'])-1}:0] ref_{n}, cand_{n};")
    for inst, typ, prefix in (("reference", reference, "ref_"), ("candidate", candidate, "cand_")):
        args = [f".{n}({n})" for n in inputs] + [f".{n}({prefix}{n})" for n in outputs]
        lines += [f"  {typ} {inst}(", "    " + ",\n    ".join(args), "  );"]
    for n in outputs:
        lines.append(f"  always @* assert (ref_{n} == cand_{n});")
    lines += ["endmodule", ""]
    return "\n".join(lines)


def main():
    workspace = next(p for p in HERE.parents if (p / "tools/oss-cad-suite-20261104").exists())
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--baseline", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--prefilter", type=Path)
    p.add_argument("--max-candidates", type=int, default=1)
    p.add_argument("--timeout", type=int, default=120)
    p.add_argument("--wrong-data", action="store_true", help="explicit negative control; never an accepted search mode")
    p.add_argument("--proof-mode", choices=("plain", "native", "factored", "coherent"), default="coherent")
    p.add_argument("--closure-summary", type=Path, default=HERE / "results/consumer_closure_v3/summary.json")
    p.add_argument("--yosys", default=str(workspace / "tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys"))
    p.add_argument("--abc", default="/usr/local/bin/abc")
    args = p.parse_args()
    if args.max_candidates < 1 or args.timeout < 1:
        p.error("max-candidates and timeout must be positive")
    out = args.output.resolve()
    out.mkdir(parents=True)
    for name in ("bank_sharing.py", "temporal.py"):
        (out / (name.removesuffix(".py") + "_source.py")).write_bytes((REPO / "odc" / name).read_bytes())
    baseline = json.loads(args.baseline.read_text())
    closure = json.loads(args.closure_summary.read_text())
    frontend_manifest = HERE.parent / "results/pre_fpu_frontend/manifest.json"
    frontend = json.loads(frontend_manifest.read_text())
    baseline_manifest = json.loads(args.baseline.with_name("manifest.json").read_text())
    closure_bound = (closure["status"] == "proved_invalid_payload_irrelevant"
        and closure["all_original_source_hashes_verified"]
        and closure["frontend_manifest_sha256"] == digest(frontend_manifest)
        and baseline_manifest["source_commit"] == closure["source_commit"]
        and baseline_manifest["source_sha256"] == frontend["original_sha256"])
    if not closure_bound:
        raise ValueError("Consumer closure is not bound to this baseline's original sources")
    top = "AluObserved"
    candidates = bank_candidates(baseline, top, pattern=r"u_alu\.u_arith_rs\.data", min_width=64)
    if args.prefilter:
        prefilter = json.loads(args.prefilter.read_text())
        if prefilter.get("hardware_design_sha256") != hashlib.sha256(json.dumps(baseline, sort_keys=True).encode()).hexdigest():
            raise ValueError("Prefilter hardware source hash mismatch")
        if [{k: v for k, v in c.items() if k != "exclusive_writes"} for c in prefilter["candidates"]] != candidates:
            raise ValueError("Prefilter belongs to different candidate list")
    else:
        prefilter = filter_exclusive_writes(baseline, top, candidates, out / "prefilter", yosys=args.yosys)
    selected = [c for c in prefilter["candidates"] if c["exclusive_writes"]][:args.max_candidates]
    reference = out / "reference.v"
    export_design(baseline, top, "AluReference", reference, args.yosys, 60)
    harness = out / "BankMiter.sv"
    harness.write_text(miter_text(baseline["modules"][top]))
    summary = {"purpose": "Program-independent phase-sharing control; no timing/environment restriction beyond reset",
               "baseline_sha256": digest(args.baseline), "implementation_sha256": digest(REPO / "odc/bank_sharing.py"),
               "harness_sha256": digest(harness), "candidate_count": len(candidates),
               "exclusive_count": sum(c["exclusive_writes"] for c in prefilter["candidates"]),
               "wrong_data_negative": args.wrong_data, "results": [], "proof_mode": args.proof_mode,
               "consumer_closure_sha256": digest(args.closure_summary), "consumer_closure_source_bound": closure_bound,
               "status": "running"}
    def prove(path, directory, spec=None):
        if args.proof_mode != "plain":
            from proof import prove as native_prove
            return native_prove(reference, path, harness, directory, yosys=args.yosys,
                timeout=args.timeout, engine="pdr", abc=args.abc,
                last_writer=(baseline, top, spec) if spec else None,
                factor_state=args.proof_mode in ("factored", "coherent"),
                coherent_alu=args.proof_mode == "coherent")
        return prove_pair(reference, path, harness, "BankMiter", directory, yosys=args.yosys,
            smtbmc="yosys-smtbmc", solver="z3", depth=12, timeout=args.timeout,
            engine="pdr", abc=args.abc, assert_state_correspondence=False, match_initial_state=False)
    identity = out / "identity.v"
    export_design(baseline, top, "AluCandidate", identity, args.yosys, 60)
    summary["identity"] = prove(identity, out / "identity_proof")
    (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    if not summary["identity"]["proven"]:
        summary["status"] = "identity_not_proven"
        (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
        raise RuntimeError("Identity proof failed; see retained evidence")
    for c in selected:
        (out / (c["id"] + ".spec.json")).write_text(json.dumps(c, indent=2) + "\n")
        variant = out / (c["id"] + ".v")
        rewritten = merge_banks(baseline, top, c, wrong_priority=args.wrong_data)
        export_design(rewritten, top, "AluCandidate", variant, args.yosys, 60)
        result = prove(variant, out / (c["id"] + "_proof"), c)
        summary["results"].append({"candidate": c, "proof": result,
                                   "accepted": result["proven"] and closure_bound and not args.wrong_data})
        (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
        print(json.dumps({"candidate": c["id"], "proven": result["proven"], "error": result.get("error")}), flush=True)
    summary["status"] = "accepted_candidate" if any(r["accepted"] for r in summary["results"]) else "no_proved_candidate"
    (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")


if __name__ == "__main__":
    main()
