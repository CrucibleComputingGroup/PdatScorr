#!/usr/bin/env python3
"""Collect compact, hash-checked evidence of the LEN5 timing ablation; runs no hardware experiment.

Small run records are copied; records above 256 KiB are gzipped deterministically. Every other
file of each collected run stays at its original build path and is listed with size and SHA-256
(Verilator object directories are summarized by file count and bytes). The script checks the
provenance links between the runs, recomputes the flip-flop constant-set relations, and writes the
ablation table (ablation.csv, ablation.json).
"""
from __future__ import annotations

import argparse
import collections
import csv
import gzip
import hashlib
import json
from pathlib import Path
import re
import shutil
import sys

HERE = Path(__file__).resolve().parent
LEN5 = HERE.parent
sys.path.insert(0, str(HERE))
from witness import field, instance  # noqa: E402

P = "ternary_reach_c1_"
C1_SHA256 = "371a91db44e992635c234ba339907654b62a6800c43d787561cea2bbbbe67b7e"
GZIP_ABOVE = 256 * 1024
BASELINE = LEN5 / "isa_baseline/evidence/final"
STREAMING = LEN5 / "program_platform/evidence/streaming_gap1_v1/summary.json"

EXPORTS = {"gap1_v2": (1, 3), "gap2_v2": (2, 3), "gap1_dlat2_v1": (1, 2), "gap1_dlat1_v1": (1, 1)}
REACHES = {"K1": ("gap1_reach_v1", "gap1_v2"), "K2": ("gap2_reach_v1", "gap2_v2"),
           "Kd2": ("gap1_dlat2_reach_v1", "gap1_dlat2_v1"), "Kd1": ("gap1_dlat1_reach_v1", "gap1_dlat1_v1")}
SWEEP = [f"timing_envelope_sweep_v1/lat{n}" for n in (4, 5, 6, 8, 12, 16, 32, 64)]
LEGAL = ["random_timing_witness_v2", "random_timing_witness_lat64_v1", *SWEEP]
NEGATIVE = ["random_timing_witness_v1", "random_timing_witness_refuse1_v1", "random_timing_witness_wide_v1"]
FIXED_WITNESSES = {"gap1_witness_v1": "K1", "gap2_witness_v1": "K2"}
COSIM = [f"gap{g}_cosim_x{x}_v2" for g in (1, 2) for x in (0, 1)]
GATESIM = [f"gap{g}_gatesim_x{x}_v1" for g in (1, 2) for x in (0, 1)]
NETLISTS = {"gap12_netlist_v1": "gap12_subst_v2", "gap2_netlist_v1": "gap2_subst_v2"}
AUDITS = {"gap1_audit_v1": "K1", "gap2_audit_v1": "K2"}
PROVENANCE = "provenance_v2"  # provenance_check.py run with the committed scripts
SUBSTITUTIONS = {"gap1_subst_v2": "K1", "gap2_subst_v2": "K2", "gap12_subst_v2": "K12", "gap1_dlat2_subst_v1": "Kd2",
                 "gap1_dlat1_subst_v1": "Kd1", "gap1_envelope_bound_subst_v1": "P"}
SUPERSEDED = {
    "gap1_v1": "export left at status running; superseded by gap1_v2",
    "gap2_v1": "export left at status running; superseded by gap2_v2",
    "gap1_subst_v1": "its map (gap1_map_v1) failed Yosys check -assert: an output port wire kept the flip-flop "
                     "net and gained the constant; substitute.py v2 rewires the port's net name too",
    "gap2_subst_v1": "as gap1_subst_v1", "gap12_subst_v1": "as gap1_subst_v1",
    "gap1_map_v1": "failed (see gap1_subst_v1)", "gap2_map_v1": "failed (see gap1_subst_v1)",
    "gap12_map_v1": "failed (see gap1_subst_v1)",
    "gap1_witness_smoke_v1": "harness smoke test", "gap2_gatesim_smoke_v1": "harness smoke test",
    "random_timing_witness_smoke_v1": "harness smoke test",
    "gap2_cosim_x0_v1": "18-run first pass; superseded by gap2_cosim_x{0,1}_v2 (132 runs each)",
    "provenance_v1": "reproduced; repeated as provenance_v2 after a docstring-only correction of export_closed.py",
}
# (row, label, information, map run, substitution run, constant set, deployments, evidence class)
ROWS = [
    ("A0", "Original fixed LEN5", "none", "isa_map_original_v1", None, None, "any", "mapped original"),
    ("C1", "Pscorr: program-word decoder + architectural RF", "ISA/program", "isa_map_registers_v1", None, None,
     "any", "conditionally certified (instruction domain)"),
    ("P", "C1 + flip-flop constants under every legal data timing", "ISA/program, any legal timing",
     "gap1_envelope_bound_map_v1", "gap1_envelope_bound_subst_v1", "P", "any legal timing",
     "simulation bound, not certified"),
    ("T3", "C1 + constants at the fixed native timing", "ISA/program + fixed timing (fetch gap 1, data latency 3)",
     "gap1_map_v2", "gap1_subst_v2", "K1", "fetch gap 1, data latency 3 (this study's native platform)",
     "certified (ternary reach) + RTL co-simulation"),
    ("T2", "C1 + constants at fixed data latency 2", "ISA/program + fixed timing (fetch gap 1, data latency 2)",
     "gap1_dlat2_map_v1", "gap1_dlat2_subst_v1", "Kd2",
     "fetch gap 1, data latency 2 (legal interface timing with the native instruction pipeline)",
     "certified (ternary reach)"),
    ("T1", "C1 + constants at fixed data latency 1", "ISA/program + fixed timing (fetch gap 1, data latency 1)",
     "gap1_dlat1_map_v1", "gap1_dlat1_subst_v1", "Kd1",
     "fetch gap 1, data latency 1 (legal interface timing with the native instruction pipeline)",
     "certified (ternary reach)"),
    ("G12", "C1 + constants common to fetch gaps 1 and 2", "ISA/program + fetch gap 1 or 2, data latency 3",
     "gap12_map_v2", "gap12_subst_v2", "K12", "fetch gap 1 (also valid at gap 2), data latency 3",
     "certified (ternary reach) + RTL and gate-level co-simulation"),
    ("G2", "C1 + constants at fetch gap 2 (outside LEN5's fetch contract)",
     "ISA/program + fixed timing (fetch gap 2, data latency 3)", "gap2_map_v2", "gap2_subst_v2", "K2",
     "fetch gap 2, data latency 3 (outside LEN5's fetch contract)",
     "certified (ternary reach) + RTL and gate-level co-simulation"),
]


def sha(path: Path) -> str:
    digest = hashlib.sha256()
    with Path(path).open("rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def load(path: Path):
    return json.loads(Path(path).read_text())


def constant_set(path: Path, key: str = "constants") -> dict:
    data = load(path)
    entries = data[key] if isinstance(data, dict) else data
    return {(c["cell"], c["bit"]): (c["net"], c["value"]) for c in entries}


def alu_row(cell: str) -> str:
    """ALU reservation-station row of a per-row flip-flop (data[N] payload or curr_state[N]), else "other"."""
    match = re.search(r"u_arith_rs\.\w+\[(\d+)\]", cell)
    return match.group(1) if match else "other"


def failure_kind(text: str) -> str:
    text = re.sub(r"^seed \d+: ", "", text)
    if " detected " in text:
        return text.split(" detected ")[0] + " (monitor)"
    if re.fullmatch(r"\d+ of \d+ stores in the \d+ cycles after the last reset", text):
        return "store count after the last reset differs from the reference"
    return text


def breakdown(keys) -> dict:
    return {"bits": len(keys),
            "by_instance": dict(collections.Counter(instance(c) for c, _ in keys).most_common()),
            "by_field": dict(collections.Counter(field(c) for c, _ in keys).most_common()),
            "by_alu_rs_row": dict(sorted(collections.Counter(alu_row(c) for c, _ in keys).items()))}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--build-root", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    b, out = args.build_root.resolve(), args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    inventory, run_dirs = [], set()

    def copy(source: Path, relative: Path) -> None:
        dest = out / relative
        dest.parent.mkdir(parents=True, exist_ok=True)
        compressed = source.stat().st_size > GZIP_ABOVE
        if compressed:
            dest = dest.with_name(dest.name + ".gz")
            with source.open("rb") as f, dest.open("wb") as raw, \
                    gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0, compresslevel=9) as g:
                shutil.copyfileobj(f, g)
            with gzip.open(dest, "rb") as g:
                assert hashlib.sha256(g.read()).hexdigest() == sha(source)
        else:
            shutil.copyfile(source, dest)
            assert sha(dest) == sha(source)
        inventory.append({"source": str(source.resolve()), "copy": str(dest.relative_to(out)), "sha256": sha(source),
                          "bytes": source.stat().st_size, "gzip": compressed})

    def run(name: str, files, required: bool = True) -> Path:
        directory = b / (name if name.startswith("isa_") else P + name)
        run_dirs.add(directory)
        for relative in files:
            source = directory / relative
            if source.exists():
                copy(source, Path("runs") / directory.relative_to(b) / relative)
            elif required:
                raise FileNotFoundError(source)
        return directory

    def mapped(name: str, design_sha: str | None) -> dict:
        directory = run(name, ["summary.json", "stat.json", "map.ys"])
        record = load(directory / "summary.json")
        execution = record["execution"]
        assert record["status"] == "mapped" and execution["returncode"] == 0 and not execution["timeout"]
        assert sha(directory / "map.log") == execution["log_sha256"]
        if design_sha is not None:
            assert record["design_sha256"] == design_sha, name
        return record

    # Reference rows: identical to the committed ISA/program evidence.
    a0 = mapped("isa_map_original_v1", None)
    c1 = mapped("isa_map_registers_v1", C1_SHA256)
    for name in ("isa_map_original_v1", "isa_map_registers_v1"):
        assert sha(b / name / "summary.json") == sha(BASELINE / name / "summary.json"), name
    assert c1["script_sha256"] == a0["script_sha256"] and c1["liberty_sha256"] == a0["liberty_sha256"]

    # Closed platforms and certified constants.
    exports = {}
    for name, (gap, latency) in EXPORTS.items():
        directory = run(name, ["summary.json", "ClosedPlatform.sv", "export_closed.py", "program.hex", "prepare.ys",
                               "export.ys", "core_export.ys"])
        record = exports[name] = load(directory / "summary.json")
        assert record["status"] == "exported" and record["design_sha256"] == C1_SHA256
        assert record["instruction_acceptance_gap"] == gap and record.get("data_reply_latency", 3) == latency
        assert record["aig_sha256"] == sha(directory / "screen.aig")
        assert record["manifest_sha256"] == sha(directory / "manifest.json")
        assert record["platform_sha256"] == sha(directory / "ClosedPlatform.sv")
    assert len({r["manifest_sha256"] for r in exports.values()}) == 1
    copy(b / f"{P}gap1_v2" / "manifest.json", Path("flip_flop_manifest.json"))
    sets, reaches = {}, {}
    for key, (name, model) in REACHES.items():
        directory = run(name, ["summary.json", "components.json", "tsim.result.txt", "tsim.log", "constants.json",
                               "trace.csv", "tsim.frames.tsv"])
        record = reaches[key] = load(directory / "summary.json")
        constants = load(directory / "constants.json")
        assert record["status"] == "certified" and constants["status"] == "certified"
        assert record["design_sha256"] == constants["design_sha256"] == C1_SHA256
        assert record["model"] == str(b / f"{P}{model}")
        assert record["model_aig_sha256"] == constants["model_aig_sha256"] == exports[model]["aig_sha256"]
        assert record["constants_sha256"] == sha(directory / "constants.json")
        assert record["trace_sha256"] == sha(directory / "trace.csv")
        assert record["script_sha256"] == sha(directory / "reach.py") == sha(HERE / "reach.py")
        assert record["tsim_source_sha256"] == sha(directory / "tsim.c") == sha(HERE / "tsim.c")
        assert record["reset_value_mismatches"] == 0 and record["never_evaluated"] == 0
        sets[key] = constant_set(directory / "constants.json")
        assert len(sets[key]) == record["constant_bits"]
    sets["K12"] = {k: v for k, v in sets["K1"].items() if sets["K2"].get(k) == v}

    # Legal timing envelope: the program-only simulation bound P.
    envelope = []
    k1 = set(sets["K1"])
    for name in LEGAL:
        directory = run(name, ["summary.json", "program_only_bound.json", "tb.sv", "platform_orig.sv",
                               "timing_witness.py", "build.log", "image.hex"])
        record, bound = load(directory / "summary.json"), load(directory / "program_only_bound.json")
        assert record["status"] == "passed" and record["envelope"] == "legal" and not record["failures"]
        assert record["design_sha256"] == bound["design_sha256"] == C1_SHA256
        assert record["model_aig_sha256"] == exports["gap1_v2"]["aig_sha256"]
        assert record["script_sha256"] == sha(directory / "timing_witness.py") == sha(HERE / "timing_witness.py")
        assert bound["status"] == "simulation_bound_not_certified" and bound["witness_status"] == "passed"
        assert bound["witness_summary_sha256"] == sha(directory / "summary.json")
        totals = record["totals"]
        assert totals["fetch_gate_closed_cycles"] == 0 and totals["service_assertion_violation_cycles"] == 0
        assert totals["max_outstanding_loads"] <= 1 and totals["max_outstanding_stores"] <= 1
        never = constant_set(directory / "program_only_bound.json")
        assert set(never) <= k1 and all(sets["K1"][k] == v for k, v in never.items())
        envelope.append({"run": name, "max_reply_delay": bound["max_reply_delay"], "runs": totals["runs"],
                         "cycles": totals["cycles"], "loads": totals["loads"], "stores": totals["stores"],
                         "witnessed_varying_in_K1": len(k1 - set(never)), "never": set(never)})
    sets["P"] = {k: sets["K1"][k] for k in set.intersection(*(e["never"] for e in envelope))}
    p_file = constant_set(b / f"{P}random_timing_witness_v2" / "program_only_bound.json")
    assert sets["P"] == p_file, "the v2 bound must already be the intersection over every legal run"
    varying = {e["run"]: k1 - e.pop("never") for e in envelope}
    assert set().union(*varying.values()) == k1 - set(sets["P"])
    for e in envelope:
        others = set().union(*(v for run_name, v in varying.items() if run_name != e["run"]))
        e["witnessed_varying_only_in_this_run"] = len(varying[e["run"]] - others)

    negative = []
    for name in NEGATIVE:
        directory = run(name, ["summary.json", "tb.sv", "platform_orig.sv", "timing_witness.py"])
        record = load(directory / "summary.json")
        assert record["status"] == "failed" and record["failures"]
        kinds = collections.Counter(failure_kind(f) for f in record["failures"])
        negative.append({"run": name, "envelope": record.get("envelope", "unbounded"),
                         "replaced_timing": record["replaced_timing"], "runs": record["totals"]["runs"],
                         "failing_seeds": len({f.split(":")[0] for f in record["failures"]}),
                         "failures": len(record["failures"]), "failure_kinds": dict(kinds.most_common()),
                         "lost_redirects": record["totals"].get("lost_redirects"),
                         "max_outstanding_loads": record["totals"]["max_outstanding_loads"]})

    # Substitutions and mapped areas.
    substitutions = {}
    for name, key in SUBSTITUTIONS.items():
        directory = run(name, ["summary.json", "applied_constants.json", "substitute.py"])
        record = substitutions[name] = load(directory / "summary.json")
        assert record["design_sha256"] == C1_SHA256
        assert record["status"] == ("substituted_simulation_bound" if key == "P" else "substituted")
        assert record["applied_constants_sha256"] == sha(directory / "applied_constants.json")
        assert record["script_sha256"] == sha(directory / "substitute.py")
        for source in record["constant_sources"]:
            assert sha(Path(source["path"])) == source["sha256"]
        applied = constant_set(directory / "applied_constants.json", None)
        assert applied == sets[key], name
    maps = {row[0]: (a0 if row[0] == "A0" else c1 if row[0] == "C1" else
                     mapped(row[3], substitutions[row[4]]["output_design_sha256"])) for row in ROWS}
    for record in maps.values():
        assert (record["script_sha256"], record["liberty_sha256"]) == (a0["script_sha256"], a0["liberty_sha256"])
        assert record["execution"]["executable_sha256"] == a0["execution"]["executable_sha256"]

    # Validation runs.
    validation = {"fixed_timing_witnesses": [], "rtl_cosimulation": [], "gate_level_cosimulation": [],
                  "netlists": [], "trace_audits": []}
    for name, key in FIXED_WITNESSES.items():
        directory = run(name, ["summary.json", "tb.sv", "platform_orig.sv", "witness.py"])
        record = load(directory / "summary.json")
        assert record["status"] == "passed" and not record["failures"]
        assert record["certified_here"]["witnessed_varying"] == 0 and record["totals"]["constant_violation_cycles"] == 0
        assert record["certified_here"]["constant_bits"] == len(sets[key])
        assert record["model_aig_sha256"] == exports[REACHES[key][1]]["aig_sha256"]
        validation["fixed_timing_witnesses"].append({"run": name, "constants": key, "runs": record["totals"]["runs"],
                                                     "cycles": record["totals"]["cycles"],
                                                     "certified_bits_witnessed_varying": 0})
    for name in COSIM + GATESIM:
        gate = "gatesim" in name
        directory = b / f"{P}{name}"
        files = ["summary.json", "tb.sv", "gatesim.py", "cells.ys"] if gate else ["summary.json", "tb.sv", "cosim.py"]
        files += sorted(p.name for p in directory.glob("platform_*.sv")) + \
            (sorted(p.name for p in directory.glob("gate_*.v")) if gate else [])
        run(name, files)
        record = load(directory / "summary.json")
        assert record["status"] == "passed" and not record["failures"] and record["design_sha256"] == C1_SHA256
        totals = record["totals"]
        assert totals["constant_violation_cycles"] == 0 and totals["service_assertion_violation_cycles"] == 0
        key = {1: "K1", 2: "K2"}[record["gap"]]
        reach = b / f"{P}{REACHES[key][0]}"
        assert record["reach"] == str(reach) and record["constants_sha256"] == sha(reach / "constants.json")
        assert record["checked_constant_bits"] == len(sets[key])
        assert record["model_aig_sha256"] == exports[REACHES[key][1]]["aig_sha256"]
        if gate:
            assert record["liberty_sha256"] == a0["liberty_sha256"]
        checked = []
        for item in record["netlists" if gate else "variants"]:
            if gate:
                netlist = b / f"{P}{item['name']}_netlist_v1"
                assert sha(netlist / "summary.json") == item["netlist_summary_sha256"]
                design = item["substitute_design_sha256"]
            else:
                assert sha(Path(item["substitute"]) / "summary.json") == item["substitute_summary_sha256"]
                design = item["design_sha256"]
            assert design == substitutions[f"{item['name']}_subst_v2"]["output_design_sha256"]
            checked.append({"variant": item["name"], "role": item["role"]})
        controls = record.get("negative_controls", {})
        assert all(c["diverged_runs"] == c["runs"] for c in controls.values())
        validation["gate_level_cosimulation" if gate else "rtl_cosimulation"].append({
            "run": name, "platform_gap": record["gap"], "runs": totals["runs"], "cycles": totals["cycles"],
            "constants_checked": key, "x_assign": record["x_assign"],
            **({"initial_state": record["initial_state"]} if gate else {}),
            "variants": checked, "equivalence_mismatch_cycles": totals["equivalence_mismatch_cycles"],
            "negative_controls_diverged": {k: f"{c['diverged_runs']}/{c['runs']}" for k, c in controls.items()}})
    for name, subst in NETLISTS.items():
        directory = run(name, ["summary.json", "stat.json", "map.ys", "map_netlist.py"])
        record = load(directory / "summary.json")
        execution = record["execution"]
        assert record["status"] == "mapped" and execution["returncode"] == 0 and not execution["timeout"]
        assert sha(directory / "map.log") == execution["log_sha256"]
        assert record["netlist_sha256"] == sha(directory / "mapped.v")
        assert record["design_sha256"] == substitutions[subst]["output_design_sha256"]
        area_run = maps["G12" if subst.startswith("gap12") else "G2"]
        assert (record["cell_area"], record["cells"]) == (area_run["cell_area"], area_run["cells"])
        validation["netlists"].append({"run": name, "cell_area": record["cell_area"], "cells": record["cells"],
                                       "equals_area_run": True})
    for name, key in AUDITS.items():
        directory = run(name, ["trace_audit.json"])
        record = load(directory / "trace_audit.json")
        reach = b / f"{P}{REACHES[key][0]}"
        assert record["status"] == "matched" and record["reach_summary_sha256"] == sha(reach / "summary.json")
        validation["trace_audits"].append({"run": name, "constants": key, "status": record["status"],
                                           "window_frames": record["window_frames"],
                                           "formal_alu_rows_admitted": record["formal_alu_rows_admitted_all_frames"]})

    # Script versions: every older version is covered by the regeneration checks.
    provenance = run(PROVENANCE, ["provenance.json"])
    provenance = load(provenance / "provenance.json")
    assert provenance["status"] == "reproduced"
    for script in ("export_closed.py", "timing_witness.py", "substitute.py", "cosim.py"):
        assert provenance["current_scripts_sha256"][script] == sha(HERE / script), script
    versions = collections.defaultdict(lambda: collections.defaultdict(list))
    for directory in sorted(run_dirs):
        for script in ("export_closed.py", "reach.py", "substitute.py", "timing_witness.py", "witness.py", "cosim.py",
                       "gatesim.py", "map_netlist.py"):
            if (directory / script).exists():
                versions[script][sha(directory / script)].append(str(directory.relative_to(b)))
    script_versions = {}
    for script, by_sha in sorted(versions.items()):
        current = sha(HERE / script)
        script_versions[script] = {"current_sha256": current, "recorded": {
            digest: {"runs": runs, "current": digest == current} for digest, runs in sorted(by_sha.items())}}
        for digest in by_sha:
            if digest != current:
                copy(Path(b / by_sha[digest][0] / script), Path("script_versions") / f"{digest[:12]}_{script}")
    reproduced = {c["run"] for c in provenance["exports"] + provenance["substitutions"]} | \
        {provenance["timing_witness_v1"]["run"]}
    older = {r for s in script_versions.values() for d in s["recorded"].values() if not d["current"] for r in d["runs"]}
    assert older <= reproduced, older - reproduced
    for versions_of_script in script_versions.values():
        for info in versions_of_script["recorded"].values():
            if not info["current"]:
                info["outputs_regenerated_identically_by_current_script"] = True

    # Constant-set relations.
    names = ["P", "K1", "Kd2", "Kd1", "K12", "K2"]
    relations = {a: {b_: {"minus": len(set(sets[a]) - set(sets[b_])),
                          "value_conflicts": sum(sets[a][k] != sets[b_][k] for k in set(sets[a]) & set(sets[b_]))}
                     for b_ in names if b_ != a} for a in names}
    assert all(set(sets["P"]) <= set(sets[k]) for k in names)
    differences = {f"{a}-P": breakdown(set(sets[a]) - set(sets["P"])) for a in ("K1", "Kd2", "Kd1", "K12", "K2")}
    differences.update({"K1-Kd2": breakdown(set(sets["K1"]) - set(sets["Kd2"])),
                        "Kd2-K1": breakdown(set(sets["Kd2"]) - set(sets["K1"])),
                        "K1-Kd1": breakdown(set(sets["K1"]) - set(sets["Kd1"])),
                        "Kd1-K1": breakdown(set(sets["Kd1"]) - set(sets["K1"])),
                        "K2-K1": breakdown(set(sets["K2"]) - set(sets["K1"])),
                        "K1-K2": breakdown(set(sets["K1"]) - set(sets["K2"]))})
    alu_rows = {key: reaches[key]["alu_rs_rows"] for key in reaches}

    # Ablation table.
    cycles = load(STREAMING)
    native, gap2_cycles = cycles["reported_cpu_cycles"], cycles["gap2_comparison"]["reported_cpu_cycles"]
    run_cycles = {"T3": native, "G12": native, "G2": gap2_cycles}
    base = maps["A0"]["cell_area"]
    bound_area = maps["P"]["cell_area"]
    rows = []
    for key, label, information, map_run, subst, constants, deployment, evidence in ROWS:
        area, cells = maps[key]["cell_area"], maps[key]["cells"]
        increment = bound_area - area if key in ("T3", "T2", "T1", "G12", "G2") else None
        rows.append({
            "row": key, "variant": label, "information": information, "evidence": evidence,
            "deployment": deployment, "flip_flop_constants": len(sets[constants]) if constants else 0,
            "cell_area_um2": area, "cells": cells, "design_sha256": maps[key]["design_sha256"],
            "reduction_vs_A0_percent": round(100 * (1 - area / base), 4),
            "increment_vs_P_um2": round(increment, 4) if increment is not None else None,
            "increment_vs_P_percent_of_A0": round(100 * increment / base, 4) if increment is not None else None,
            "increment_vs_P_percent_of_P": round(100 * increment / bound_area, 4) if increment is not None else None,
            "program_cycles": run_cycles.get(key),
            "equal_runtime_to_P": key != "G2",
            "legal_on_LEN5": key != "G2",
            "map_run": map_run, "substitution_run": subst})
    with (out / "ablation.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    ablation = {
        "status": "ablation_recorded",
        "question": "Pscorr with ISA/program constraints versus the same constraints plus fixed timing, "
                    "on unchanged LEN5 RTL and capacities, at equal runtime",
        "rows": rows,
        "notes": {
            "P": "Optimistic bound, not certified: K1 minus every bit witnessed varying in any legal-envelope run. "
                 "A certified program-only constant set from the same engine would be a subset of P (assuming it "
                 "certifies nothing outside K1 and mapping is monotone), so each increment over P is a lower bound.",
            "equal_runtime": "Each row is C1 with flip-flops that are constant in its deployment replaced by their "
                             "constants, so in that deployment it produces A0's outputs in the same cycles "
                             "(certified by ternary reachability relative to C1 for T3, T2, T1, G12, and G2; "
                             "simulation evidence only for P; C1 under its instruction-domain condition). Runtime "
                             f"is the deployment's: {native} cycles for the program at the native timing (fetch "
                             "gap 1, data latency 3). Data latencies 2 and 1 were not timed.",
            "data_latency": "LEN5's memory emulator replies after 1 + PIPE_NUM cycles with its data answer "
                            "register skipped (this study's platform: PIPE_NUM=2, three cycles). Latencies 2 and 1 "
                            "need PIPE_NUM 1 or 0, which also shortens instruction responses; T2 and T1 keep the "
                            "native instruction pipeline, so they model legal interface timings, not an emulator "
                            "setting.",
            "G2": f"Fetch gap 2 is outside LEN5's fetch contract (a refusal can lose a redirect) and the program "
                  f"takes {gap2_cycles} cycles instead of {native}.",
            "C1": "Conditionally certified under the instruction-domain assumption; see isa_baseline/evidence/final."},
        "legal_envelope": envelope,
        "negative_controls": negative,
        "constant_set_sizes": {k: len(v) for k, v in sets.items()},
        "constant_set_relations": relations,
        "differences": differences,
        "alu_rs_rows_certified": alu_rows,
        "validation": validation,
        "script_versions": script_versions,
        "superseded_runs": {f"{P}{k}": {"status": next((load(f)["status"] for f in (b / f"{P}{k}" / "summary.json",
                                                                                  b / f"{P}{k}" / "provenance.json")
                                                        if f.exists()), None), "reason": v}
                            for k, v in SUPERSEDED.items()},
    }
    (out / "ablation.json").write_text(json.dumps(ablation, indent=2) + "\n")

    copy(Path(__file__), Path("collector_source.py"))
    copy(HERE / "provenance_check.py", Path("provenance_check_source.py"))
    copied = {x["source"] for x in inventory}
    omitted, objects = [], collections.Counter()
    for directory in sorted(run_dirs):
        for f in sorted(directory.rglob("*")):
            if not f.is_file() or str(f.resolve()) in copied:
                continue
            relative = f.relative_to(b)
            if "obj" in relative.parts:
                top = Path(*relative.parts[:relative.parts.index("obj") + 1])
                objects[str(top), "files"] += 1
                objects[str(top), "bytes"] += f.stat().st_size
                continue
            omitted.append((str(relative), f.stat().st_size, sha(f)))
    with gzip.GzipFile(out / "omitted_files.tsv.gz", "wb", mtime=0) as g:
        g.write("".join(f"{p}\t{n}\t{h}\n" for p, n, h in omitted).encode())
    record = {
        "status": "ablation_evidence_collected",
        "method": "Pscorr flip-flop constants by ternary reachability on closed fixed-timing platforms, applied to the "
                  "C1 netlist and mapped to SKY130 HD with the same script, liberty, and Yosys as A0/C1",
        "original_full_data_root": str(b),
        "c1_design_sha256": C1_SHA256,
        "mapping": {"script_sha256": a0["script_sha256"], "liberty_sha256": a0["liberty_sha256"],
                    "executable_sha256": a0["execution"]["executable_sha256"]},
        "files": inventory,
        "omitted_files": {"list": "omitted_files.tsv.gz (path relative to the build root, bytes, sha256)",
                          "count": len(omitted), "bytes": sum(n for _, n, _ in omitted)},
        "omitted_object_directories": {d: {"files": objects[d, "files"], "bytes": objects[d, "bytes"]}
                                       for d in sorted({d for d, _ in objects})},
        "no_new_simulation_or_synthesis": True}
    (out / "manifest.json").write_text(json.dumps(record, indent=2) + "\n")
    (out / "SHA256SUMS").write_text("".join(f"{sha(f)}  {f.relative_to(out)}\n" for f in sorted(out.rglob("*"))
                                            if f.is_file() and f.name != "SHA256SUMS"))
    print(json.dumps({"files": sum(f.is_file() for f in out.rglob("*")),
                      "bytes": sum(f.stat().st_size for f in out.rglob("*") if f.is_file()), "output": str(out),
                      "rows": [(r["row"], r["cell_area_um2"], r["increment_vs_P_um2"]) for r in rows]}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
