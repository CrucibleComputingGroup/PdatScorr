#!/usr/bin/env python3
"""Check that the committed scripts reproduce the recorded runs made with older script versions.

None of these checks runs Yosys, Verilator, or the ternary engine:

1. export_closed.py: regenerate the ClosedPlatform.sv of every recorded export (fetch gap 1/2,
   data latency 3/2/1) and compare it byte for byte with the recorded file.
2. timing_witness.py: regenerate the unbounded-timing platform and testbench of
   random_timing_witness_v1 and compare them with the source hashes that run recorded.
3. substitute.py: re-apply the recorded constant sets to the same input design and compare the
   output design and applied-constant hashes with the recorded *_subst_v2 runs.

The record is written to --output (a new directory); the exit status is nonzero on any mismatch.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import export_closed as ec  # noqa: E402
import timing_witness as tw  # noqa: E402
from cosim import PROBES, data_image, fill, hex_vector, sim_platform  # noqa: E402
from program_rom import read_image  # noqa: E402

PREFIX = "ternary_reach_c1_"
C1_SHA256 = "371a91db44e992635c234ba339907654b62a6800c43d787561cea2bbbbe67b7e"


def sha(path: Path) -> str:
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def sha_text(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def check_exports(build: Path, ports: dict) -> list[dict]:
    results = []
    for name in ("gap1_v2", "gap2_v2", "gap1_dlat2_v1", "gap1_dlat1_v1"):
        run = build / f"{PREFIX}{name}"
        summary = json.loads((run / "summary.json").read_text())
        latency = summary.get("data_reply_latency", ec.NATIVE_DATA_LATENCY)
        text = ec.closed_harness(ports, summary["instruction_acceptance_gap"], summary["admission_threshold_property"],
                                 read_image(run / "program.hex"), latency)
        recorded = run / "ClosedPlatform.sv"
        results.append({"run": run.name, "gap": summary["instruction_acceptance_gap"], "data_reply_latency": latency,
                        "recorded_script_sha256": summary["helpers_sha256"]["export_closed.py"],
                        "recorded_platform_sha256": sha(recorded),
                        "summary_platform_sha256": summary["platform_sha256"],
                        "regenerated_platform_sha256": sha_text(text),
                        "identical": text == recorded.read_text() and summary["platform_sha256"] == sha(recorded)})
    return results


def check_timing_witness_v1(build: Path, ports: dict, records: list[dict]) -> dict:
    model, run = build / f"{PREFIX}gap1_v2", build / f"{PREFIX}random_timing_witness_v1"
    summary = json.loads((run / "summary.json").read_text())
    outputs = sorted((n, len(p["bits"])) for n, p in ports.items() if p["direction"] == "output" and n not in PROBES)
    base, words = data_image(Path(summary["evidence"]) / "data.hex")
    zero = hex_vector([0] * len(records))
    platform, _ = sim_platform(tw.randomized_platform((model / "ClosedPlatform.sv").read_text()),
                               "orig", "Core_orig", outputs)
    bench = fill(tw.timing_testbench(), W=len(records), K=sum(w for _, w in outputs), NV=1, THRESHOLD=0,
                 CMASK=zero, CVAL=zero, WMASK=hex_vector([int(r["reset"] is not None) for r in records]),
                 WVAL=hex_vector([r["reset"] or 0 for r in records]), IMG_BASE=f"{base:x}", IMG_WORDS=len(words),
                 INSTANCES="", CHECKS="")
    recorded = summary["sources_sha256"]
    return {"run": run.name, "recorded_script_sha256": summary["script_sha256"],
            "recorded_platform_sha256": recorded["platform_orig.sv"], "regenerated_platform_sha256": sha_text(platform),
            "recorded_testbench_sha256": recorded["tb.sv"], "regenerated_testbench_sha256": sha_text(bench),
            "identical": sha_text(platform) == recorded["platform_orig.sv"] and sha_text(bench) == recorded["tb.sv"]}


def check_substitutions(build: Path, work: Path) -> list[dict]:
    results = []
    for name in ("gap1_subst_v2", "gap2_subst_v2", "gap12_subst_v2"):
        run = build / f"{PREFIX}{name}"
        summary = json.loads((run / "summary.json").read_text())
        sources = [Path(s["path"]) for s in summary["constant_sources"]]
        if [sha(p) for p in sources] != [s["sha256"] for s in summary["constant_sources"]]:
            raise ValueError(f"{run.name}: a constant source changed since the run")
        out = work / name
        subprocess.run([sys.executable, str(HERE / "substitute.py"), "--design", summary["design"],
                        "--constants", *map(str, sources), "--output", str(out)], check=True, stdout=subprocess.DEVNULL)
        again = json.loads((out / "summary.json").read_text())
        keys = ("output_design_sha256", "applied_constants_sha256", "applied_constant_bits", "rewired_connections")
        results.append({"run": run.name, "recorded_script_sha256": summary["script_sha256"],
                        "current_script_sha256": again["script_sha256"],
                        **{f"recorded_{k}": summary[k] for k in keys[:3]}, **{f"regenerated_{k}": again[k] for k in keys[:3]},
                        "identical": all(summary[k] == again[k] for k in keys)})
    return results


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--build-root", type=Path, required=True)
    ap.add_argument("--work", type=Path, required=True, help="New scratch directory for regenerated designs")
    ap.add_argument("--output", type=Path, required=True, help="New directory for provenance.json")
    args = ap.parse_args()
    build, out, work = args.build_root.resolve(), args.output.resolve(), args.work.resolve()
    out.mkdir(parents=True, exist_ok=False)
    work.mkdir(parents=True, exist_ok=False)
    design_path = Path(json.loads((build / f"{PREFIX}gap1_v2" / "summary.json").read_text())["design"])
    if sha(design_path) != C1_SHA256:
        raise ValueError("The exports' input design is not the C1 design")
    design = json.loads(design_path.read_text())
    records = ec.flip_flop_manifest(design)
    ports = ec.observed_design(design, records)["modules"]["datapath"]["ports"]
    record = {"exports": check_exports(build, ports), "timing_witness_v1": check_timing_witness_v1(build, ports, records),
              "substitutions": check_substitutions(build, work)}
    checks = record["exports"] + [record["timing_witness_v1"]] + record["substitutions"]
    record = {"status": "reproduced" if all(c["identical"] for c in checks) else "mismatch",
              "scope": "Committed scripts regenerate the recorded artifacts of runs made with older script versions.",
              "design_sha256": C1_SHA256,
              "current_scripts_sha256": {p.name: sha(p) for p in sorted(HERE.glob("*.py")) if p.name != "__init__.py"},
              **record}
    (out / "provenance.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({"status": record["status"], "checks": len(checks)}))
    return 0 if record["status"] == "reproduced" else 1


if __name__ == "__main__":
    raise SystemExit(main())
