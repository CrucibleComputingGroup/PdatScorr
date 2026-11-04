#!/usr/bin/env python3
"""Prove region invariants and unreachable comparator outcomes on actual RTL.

Uses the locally acquired yosys-slang toolchain. Runs reset-based BMC base
checks AND temporal induction; neither result alone is accepted as complete.
The original queue modules are unchanged. A separate environment harness
provides arbitrary inputs and the explicit all-executed region assumptions.
"""
import hashlib
import json
import subprocess
import time
from pathlib import Path

from prove_nonalias import HERE, SOURCE_HASHES


def main():
    root = HERE.parents[2]
    src = HERE.parent / "rsd/Processor/Src"
    for relative, expected in SOURCE_HASHES.items():
        if hashlib.sha256((src / relative).read_bytes()).hexdigest() != expected:
            raise RuntimeError(f"Source changed: {relative}")
    toolbin = root / "tools/oss-cad-suite-20261104/oss-cad-suite/bin"
    out = HERE / "results/actual_lsq"
    out.mkdir(parents=True, exist_ok=True)
    # The checked-in minimal file list preserves upstream package order.
    # Every file is read directly from the pinned, untouched RTL checkout.
    files = [str(src / relative) for relative in
             (HERE / "rtl_sources.txt").read_text().splitlines() if relative]
    command = ["read_slang", "--single-unit", "--top", "LSQRegionProof", f"-I{src}",
               "-DRSD_SYNTHESIS", "-DRSD_SYNTHESIS_DESIGN_COMPILER", "-DREF=input",
               "-DRSD_DISABLE_DEBUG_REGISTER", "-DRSD_DISABLE_PERFORMANCE_COUNTER",
               "-DRSD_MARCH_INT_ISSUE_WIDTH=2", "-DRSD_MARCH_FP_PIPE", "-DRSD_ENABLE_ZBA", "-DRSD_ENABLE_ZICOND",
               *files, str(HERE / "LSQRegionProof.sv")]
    smt = out / "model.smt2"
    ys = out / "formal.ys"
    ys.write_text(" ".join(command) + "\nprep -top LSQRegionProof -flatten\n"
                  "memory_map\nopt_clean\ndffunmap\nchformal -lower\n"
                  f"write_smt2 -wires {smt}\n")
    executions = []

    def run(name, cmd, timeout=120):
        started = time.monotonic()
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        log = result.stdout + result.stderr
        (out / f"{name}.log").write_text(log)
        executions.append({"name": name, "command": cmd, "returncode": result.returncode,
                           "seconds": time.monotonic() - started})
        if result.returncode:
            raise RuntimeError(f"{name} failed; see {out / (name + '.log')}")
        return log

    run("elaborate", [str(toolbin / "yosys"), "-m", "slang", "-s", str(ys)])
    model = smt.read_text()
    assert_count = model.count("; yosys-smt2-assert ")
    assume_count = model.count("; yosys-smt2-assume ")
    cover_count = model.count("; yosys-smt2-cover ")
    if (assert_count, assume_count, cover_count) != (36, 3, 1):
        raise RuntimeError(f"Unexpected formal property counts: {assert_count}, {assume_count}, {cover_count}")
    for name, flags in [("base", []), ("induction", ["-i"])]:
        log = run(name, [str(toolbin / "yosys-smtbmc"), "-s", "z3", "-t", "4", *flags, str(smt)], timeout=120)
        if "Status: PASSED" not in log:
            raise RuntimeError(f"{name} did not prove all assertions")
    log = run("cover_nonvacuity", [str(toolbin / "yosys-smtbmc"), "-s", "z3", "-t", "4", "-c", str(smt)], timeout=120)
    if "Status: PASSED" not in log or "Reached cover statement" not in log:
        raise RuntimeError("No actual-RTL trace demonstrating nonvacuity")
    result = {"status": "passed", "scope": "Actual unmodified RSD LoadQueue/StoreQueue RTL: inductive region invariants and zero historical comparator/forwarding outcomes under the explicit harness contract. Not complete processor equivalence or application-contract proof.",
              "rtl_revision": "7b65f6ba0bce58d4d859082660123b7100aae975",
              "source_sha256": SOURCE_HASHES, "harness_sha256": hashlib.sha256((HERE / "LSQRegionProof.sv").read_bytes()).hexdigest(),
              "executions": executions,
              "property_counts": {"assert": assert_count, "assume": assume_count, "cover": cover_count},
              "all_elaboration_source_sha256": {path: hashlib.sha256(Path(path).read_bytes()).hexdigest() for path in files},
              "assumptions": ["Initial reset asserted", "Every executed load has physical address[21:16]==0", "Every executed store has physical address[21:16]!=0"],
              "notes": ["Release, allocation, entry selection, recovery, data, masks, and validity are arbitrary inputs; this overapproximates legal core traffic.", "Read_slang defaults to synthesis behavior; RSD simulation-only internal assertions are disabled; all harness assertions are explicit and checked."]}
    (out / "summary.json").write_text(json.dumps(result, indent=2) + "\n")
    print("PASS: actual RTL reset base and temporal induction")


if __name__ == "__main__":
    main()
