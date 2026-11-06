#!/usr/bin/env python3
"""Certify constant core flip-flop bits by ternary reachability on a closed model.

Runs tsim (ternary simulation, lasso closure, re-reset coverage) on a model made
by export_closed.py. A flip-flop bit is reported constant only when the closed
invariant check passes and its observed Q value is the same binary value in
every invariant cube under every admitted reset value. Reset flip-flops must
then hold their reset value; any mismatch rejects the whole run.
"""
from __future__ import annotations

import argparse
import collections
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
sys.path.insert(0, str(REPO))
from odc.temporal import digest, run_command  # noqa: E402

TRACE_OUTPUTS = ("obs_insert", "obs_index", "obs_fetch", "obs_fetch_addr", "obs_store",
                 "obs_store_addr", "obs_load", "obs_flush")


def compile_tsim(out: Path) -> dict:
    env = dict(os.environ, PATH="/usr/bin:/bin")
    argv = ["gcc", "-O2", "-std=c11", "-Wall", "-Wextra", "-o", str(out / "tsim"), str(out / "tsim.c")]
    result = subprocess.run(argv, env=env, capture_output=True, text=True, check=True)
    version = subprocess.run(["gcc", "--version"], env=env, capture_output=True, text=True, check=True)
    return {"argv": argv, "stderr": result.stderr, "compiler": version.stdout.splitlines()[0],
            "binary_sha256": digest(out / "tsim")}


def component(cell: str) -> str:
    name = cell.removeprefix("$driver$")
    return re.sub(r"\[\d+\]", "[*]", name)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--model", type=Path, required=True)
    ap.add_argument("--frames", type=int, default=4096)
    ap.add_argument("--max-period", type=int, default=2048)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--timeout", type=int, default=3600)
    args = ap.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    model = args.model.resolve()
    shutil.copyfile(HERE / "tsim.c", out / "tsim.c")
    shutil.copyfile(Path(__file__), out / "reach.py")
    summary = json.loads((model / "summary.json").read_text())
    if summary.get("status") != "exported" or digest(model / "screen.aig") != summary["aig_sha256"] \
            or digest(model / "manifest.json") != summary["manifest_sha256"]:
        raise ValueError("Model directory does not match its export record")
    manifest = json.loads((model / "manifest.json").read_text())
    records = manifest["records"]
    record = {"status": "running", "model": str(model), "model_aig_sha256": summary["aig_sha256"],
              "model_manifest_sha256": summary["manifest_sha256"], "design_sha256": summary["design_sha256"],
              "instruction_acceptance_gap": summary["instruction_acceptance_gap"],
              "frames": args.frames, "max_period": args.max_period, "compile": compile_tsim(out),
              "script_sha256": digest(Path(__file__)), "tsim_source_sha256": digest(out / "tsim.c")}
    (out / "summary.json").write_text(json.dumps(record, indent=2) + "\n")
    run = run_command([str(out / "tsim"), str(model / "screen.aig"), str(manifest["reset_input_index"]),
                       str(args.frames), str(args.max_period), str(out / "tsim")], out / "tsim.log", args.timeout)
    record["run"] = run
    result = {}
    for line in (out / "tsim.result.txt").read_text().splitlines():
        key, _, value = line.partition(" ")
        result[key] = value
    record["result"] = result
    ok = run["returncode"] == 0 and not run["timeout"] and result.get("invariant_ok") == "1"
    outjoin = (out / "tsim.outjoin.bin").read_bytes()
    constants, mismatches, never = [], [], 0
    by_component = collections.defaultdict(lambda: [0, 0])
    for r in records:
        value = outjoin[r["aig_output"]]
        key = component(r["cell"])
        by_component[key][0] += 1
        if value == 3:
            never += 1
        elif value in (0, 1):
            if r["reset"] is not None and value != r["reset"]:
                mismatches.append(r)
            constants.append({"cell": r["cell"], "bit": r["bit"], "net": r["net"], "value": value,
                              "type": r["type"], "reset": r["reset"]})
            by_component[key][1] += 1
    if never or mismatches:
        ok = False
    rows = {}
    for r in records:
        m = re.search(r"u_alu_unit\.u_arith_rs\.(?:data|curr_state)\[(\d)\]", r["cell"])
        if m:
            entry = rows.setdefault(int(m.group(1)), [0, 0])
            entry[0] += 1
            entry[1] += outjoin[r["aig_output"]] in (0, 1)
    # Main-trajectory audit trace of observation outputs.
    width = int(result["header"].split()[3])
    frames = args.frames + 1
    data = (out / "tsim.outs.bin").read_bytes()
    if len(data) != width * frames:
        raise ValueError("Unexpected trace size")
    names = [n for n in TRACE_OUTPUTS if n in manifest["observation_outputs"]]
    admitted = collections.Counter()
    with (out / "trace.csv").open("w") as trace:
        trace.write("frame," + ",".join(names) + "\n")
        for t in range(frames):
            row = data[t * width:(t + 1) * width]
            values = []
            for name in names:
                bits = [row[i] for i in manifest["observation_outputs"][name]]
                values.append("x" if 2 in bits else str(sum(b << k for k, b in enumerate(bits))))
            trace.write(f"{t}," + ",".join(values) + "\n")
            fields = dict(zip(names, values))
            if fields.get("obs_insert") == "1":
                admitted[fields.get("obs_index")] += 1
            elif fields.get("obs_insert") == "x":
                admitted["unknown"] += 1
    record.update(
        status="certified" if ok else "rejected",
        flip_flop_bits=len(records), constant_bits=len(constants),
        constant_zero_bits=sum(c["value"] == 0 for c in constants),
        constant_one_bits=sum(c["value"] == 1 for c in constants),
        reset_value_mismatches=len(mismatches), never_evaluated=never,
        alu_rs_rows={str(k): {"bits": v[0], "constant_bits": v[1]} for k, v in sorted(rows.items())},
        main_trajectory_alu_admissions=dict(sorted(admitted.items())),
        trace_sha256=digest(out / "trace.csv"))
    (out / "constants.json").write_text(json.dumps({
        "status": record["status"], "model_aig_sha256": summary["aig_sha256"],
        "design_sha256": summary["design_sha256"], "gap": summary["instruction_acceptance_gap"],
        "constants": constants if ok else []}) + "\n")
    (out / "components.json").write_text(json.dumps(
        {k: {"bits": v[0], "constant_bits": v[1]} for k, v in sorted(by_component.items())}, indent=1) + "\n")
    record["constants_sha256"] = digest(out / "constants.json")
    record["components_sha256"] = digest(out / "components.json")
    (out / "summary.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({k: record[k] for k in ("status", "flip_flop_bits", "constant_bits", "alu_rs_rows",
                                             "main_trajectory_alu_admissions")}))
    print(json.dumps(result))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
