#!/usr/bin/env python3
"""Actual LEN5 functional-only bad-write and raw-local-payload falsifiers."""
from __future__ import annotations
import argparse
import copy
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
sys.path.insert(0, str(REPO))
from odc.bank_sharing import merge_banks
from odc.temporal import digest, export_design, prove_pair, run_command
from run import miter_text


def main():
    workspace = next(p for p in HERE.parents if (p / "tools/oss-cad-suite-20261104").exists())
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--baseline", type=Path, required=True)
    p.add_argument("--bank-spec", type=Path, required=True)
    p.add_argument("--mode", choices=("wrong_data", "raw_local_alu"), required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--timeout", type=int, default=60)
    args = p.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True)
    original = json.loads(args.baseline.read_text())
    spec = json.loads(args.bank_spec.read_text())
    if args.mode == "raw_local_alu":
        # Deliberately expose the pre-arbitration ALU payload even when invalid.
        # This is an observation change in BOTH copies, not a hardware cut.
        m = original["modules"]["AluObserved"]
        bits = m["netnames"]["alu_data"]["bits"]
        m["ports"]["raw_alu_payload"] = {"direction": "output", "bits": bits}
        m["netnames"]["raw_alu_payload"] = {"hide_name": 0, "bits": bits, "attributes": {}}
    candidate = merge_banks(original, "AluObserved", spec, wrong_priority=args.mode == "wrong_data")
    yosys = str(workspace / "tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys")
    ref, cand, harness = out / "reference.v", out / "candidate.v", out / "BankMiter.sv"
    export_design(original, "AluObserved", "AluReference", ref, yosys, 60)
    export_design(candidate, "AluObserved", "AluCandidate", cand, yosys, 60)
    harness.write_text(miter_text(original["modules"]["AluObserved"]))
    proof = prove_pair(ref, cand, harness, "BankMiter", out / "proof", yosys=yosys,
        smtbmc="yosys-smtbmc", solver="z3", depth=12, timeout=args.timeout,
        engine="pdr", abc="/usr/local/bin/abc", assert_state_correspondence=False, match_initial_state=False)
    summary = {"mode": args.mode, "baseline_sha256": digest(args.baseline),
               "bank_spec_sha256": digest(args.bank_spec), "proof_sha256": digest(out / "proof/proof.json"),
               "status": "unknown", "boundary": "global qualified CDB + all ready/valid outputs",
               "state_correspondence_assertions": 0, "initial_state_assumptions": 0,
               "environment": "common initial native reset only"}
    if "pdr" in proof:
        log = Path(proof["pdr"]["log"]).read_text()
        failed = re.findall(r"(?m)^Output\s+\d+[^\n]*\bwas asserted\b[^\n]*", log)
        if proof["pdr"]["returncode"] == 0 and not proof["pdr"]["timeout"] and len(failed) == 1:
            summary["status"] = "functional_counterexample"
            summary["failure"] = failed
            command = proof["pdr"]["argv"][2]
            command += '; testcex -a'
            command += f'; write_cex -n -c "{out / "counterexample.txt"}"'
            command += f'; write_cex -a "{out / "counterexample.aiw"}"'
            (out / "witness.abc").write_text(command + "\n")
            execution = run_command(["/usr/local/bin/abc", "-c", command], out / "witness.log", args.timeout + 5)
            witness_log = (out / "witness.log").read_text()
            summary["witness"] = execution
            summary["witness_validated"] = (execution["returncode"] == 0 and not execution["timeout"]
                and "Main AIG: The cex is correct." in witness_log
                and not re.search(r"(?im)^.*\b(error|incorrect|verification failed)\b", witness_log))
            if summary["witness_validated"]:
                summary["witness_sha256"] = {n: digest(out / n) for n in ("counterexample.txt", "counterexample.aiw")}
    if args.mode == "raw_local_alu":
        summary["boundary"] += "; ALSO raw pre-arbitration ALU payload, deliberately including invalid cycles"
    (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary))


if __name__ == "__main__":
    main()
