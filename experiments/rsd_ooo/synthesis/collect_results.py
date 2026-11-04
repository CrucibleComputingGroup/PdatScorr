#!/usr/bin/env python3
"""Collect completed, matched RSD runs without accepting partial tool output."""
import argparse
import hashlib
import json
import re
from pathlib import Path


def aig_header(path):
    with path.open("rb") as file:
        tokens = file.readline().decode("ascii").split()
    if tokens[0] not in ["aig", "aag"]:
        raise ValueError(f"Invalid AIGER header: {path}")
    values = list(map(int, tokens[1:])) + [0] * 4
    return dict(zip(["variables", "inputs", "latches", "outputs", "ands", "bad", "constraints", "justice", "fairness"], values))


def library_cells(path):
    """Read cell-level area and sequential declarations from this Liberty."""
    text = path.read_text()
    starts = list(re.finditer(r'\bcell\s*\(\s*"?([^"\s)]+)"?\s*\)\s*\{', text))
    cells = {}
    for i, match in enumerate(starts):
        body = text[match.end():starts[i + 1].start() if i + 1 < len(starts) else len(text)]
        area = re.search(r'\barea\s*:\s*([\d.eE+-]+)\s*;', body)
        if area:
            cells[match[1]] = {
                "area": float(area[1]),
                "sequential": bool(re.search(r'\b(?:ff|latch|ff_bank|latch_bank)\s*\(', body)),
            }
    return cells


def breakdown(modules, liberty):
    library = library_cells(liberty)
    result = {"sequential": {"cells": 0, "cell_area_um2": 0.0},
              "combinational": {"cells": 0, "cell_area_um2": 0.0},
              "unmapped_types": {}}
    for module in modules:
        for name, count in module["num_cells_by_type"].items():
            name = name.lstrip("\\")
            if name not in library:
                result["unmapped_types"][name] = result["unmapped_types"].get(name, 0) + count
                continue
            cell = library[name]
            group = result["sequential" if cell["sequential"] else "combinational"]
            group["cells"] += count
            group["cell_area_um2"] += count * cell["area"]
    return result


def physical(path):
    log = path / "mapping.log"
    if not log.exists():
        return {"status": "not_started"}
    text = log.read_text(errors="replace")
    areas = re.findall(r"Chip area for (?:top )?module[^:]*:\s*([\d.]+)", text)
    # The runner records completion after observing exit status zero.  A final
    # stat alone is insufficient, and -T suppresses Yosys's ordinary footer.
    manifest_path = path / "manifest.json"
    manifest = json.loads(manifest_path.read_text()) if manifest_path.exists() else {}
    if manifest.get("status") != "complete":
        return {"status": manifest.get("status", "incomplete"), "log": str(log)}
    if not areas or "ERROR:" in text:
        return {"status": "invalid_completed_output", "log": str(log)}
    data = json.loads((path / "area.json").read_text())
    modules = list(data["modules"].values())
    cells = sum(m["num_cells"] for m in modules)
    result = {
        "status": "complete", "cell_area_um2": float(areas[-1]),
        "cells": cells, "log": str(log), "area_json": str(path / "area.json"),
        "map_script_sha256": hashlib.sha256((path / "map.ys").read_bytes()).hexdigest(),
    }
    result["area_breakdown"] = breakdown(modules, Path(manifest["library"]))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--results", type=Path, default=Path(__file__).resolve().parents[1] / "results/synthesis")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    root = args.results.resolve()
    summary = {
        "physical_core": {
            "flow_family": "legacy_verilog_reread_physical",
            "scope": "RSD Core, including flop-mapped caches/register memories; no SRAM macros, SoC peripherals, placement, or routing",
            "flow": "Legacy Yosys0.33 normalized-Verilog reread before AIGER zinit; assumptions removed; identical SKY130 HD mapping",
            "original": physical(root / "core_direct_original"),
            "region_cut": physical(root / "core_direct_region_cut"),
        },
        "physical_core_modern_inprocess": {
            "scope": "Whole Core, flop-mapped memories; distinct matched modern in-process physical flow",
            "flow": "Same prepared source/normalization; no Verilog reread, no zinit; explicit legacy strash/dretime/map using system yosys-abc and same SKY130 Liberty",
            "original": physical(root / "core_modern_direct_original"),
            "region_cut": physical(root / "core_modern_direct_region_cut"),
            "combined_cut": physical(root / "core_modern_direct_combined"),
            "scheduler_cut": physical(root / "core_modern_direct_scheduler"),
        },
        "formal_aig_core": {
            "scope": "AIGER formal model including zinit arbitrary-initial-state input/mux encoding; not directly comparable to physical_core area",
            "runs": {},
        },
        "physical_registerfile_capacity": {
            "scope": "RegisterFile component capacity/performance control, not Pscorr or same-capacity pruning; every functional read/write port retained",
            "flow": "Matched guarded64/48 source snapshots; direct pre-zinit RTL; same Yosys0.33/ABC-fast/SKY130 flow",
            "capacity": "INT and FP banks each change64→48 entries; identical explicit reset guard in both snapshots",
            "observation": "299 nominal input bits including clock/reset,429 raw output bits across every functional read/write port; no assumptions or masks",
            "initialization": "Direct normalized RTL, no AIGER-zinit initialization model",
            "guard64": physical(root / "registerfile_guard64/direct_map"),
            "guard48": physical(root / "registerfile_guard48/direct_map"),
            "source_boundary_audit": str(root.parent / "prf_guard/source_boundary_audit.json"),
            "physical_mapping_audit": str(root / "registerfile_physical_audit.json"),
            "source_manifests": {name: str(root / ("registerfile_" + name) / "manifest.json") for name in ["guard64", "guard48"]},
        },
    }
    for family in ["physical_core", "physical_core_modern_inprocess"]:
        physical_runs = summary[family]
        if all(physical_runs[k]["status"] == "complete" for k in ["original", "region_cut"]):
            baseline = physical_runs["original"]["cell_area_um2"]
            modified = physical_runs["region_cut"]["cell_area_um2"]
            physical_runs["reduction_percent"] = 100 * (baseline - modified) / baseline
    modern = summary["physical_core_modern_inprocess"]
    if all(modern[name]["status"] == "complete" for name in ["original", "scheduler_cut"]):
        modern["scheduler_reduction_percent_vs_original"] = 100 * (modern["original"]["cell_area_um2"] - modern["scheduler_cut"]["cell_area_um2"]) / modern["original"]["cell_area_um2"]
    if modern["combined_cut"]["status"] == "complete":
        combined = modern["combined_cut"]["cell_area_um2"]
        for control, key in [("original", "combined_reduction_percent_vs_original"), ("region_cut", "combined_incremental_reduction_percent_vs_region")]:
            if modern[control]["status"] == "complete":
                denominator = modern[control]["cell_area_um2"]
                modern[key] = 100 * (denominator - combined) / denominator
    (root / "whole_core_modern_physical_summary.json").write_text(json.dumps(modern, indent=2) + "\n")
    prf = summary["physical_registerfile_capacity"]
    if all(prf[name]["status"] == "complete" for name in ["guard64", "guard48"]):
        prf["reduction_percent"] = 100 * (prf["guard64"]["cell_area_um2"] - prf["guard48"]["cell_area_um2"]) / prf["guard64"]["cell_area_um2"]
        (root / "registerfile_direct_summary.json").write_text(json.dumps(prf, indent=2) + "\n")
    summary["component_summaries"] = {}
    for name in ["lsq_direct_summary.json", "lsq_lemma_reset_summary.json", "scheduler_direct_summary.json", "scheduler_lemma_reset_summary.json"]:
        path = root / name
        if path.exists():
            summary["component_summaries"][name] = {"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
    for name in ["base_core_final", "isa_core_final", "nonalias_core_final", "isa_nonalias_core_final", "isa_region_assume_core_final_v2", "isa_region_lemmas_core_final"]:
        for mode in ["mapped_scorr", "mapped_no_scorr", "mapped_scorr_constants", "logic_scorr_prebalanced", "logic_no_scorr_prebalanced"]:
            file = root / name / mode / "result.json"
            if file.exists():
                run = json.loads(file.read_text())
                run["logic_complete"] = bool(run.get("optimized") and run.get("stages") and run["stages"][0].get("status") == "passed")
                run["mapping_complete"] = run.get("status") == "complete" and "cell_area_um2" in run
                if run.get("stages") and run["stages"][0].get("status") == "passed":
                    for model in ["prebalanced.aig", "optimized_with_constraints.aig"]:
                        if (file.parent / model).exists():
                            run[model] = aig_header(file.parent / model)
                summary["formal_aig_core"]["runs"][name + "/" + mode] = run
    runs = summary["formal_aig_core"]["runs"]
    planned = [(name, "mapped_scorr") for name in ["base_core_final", "isa_core_final", "nonalias_core_final", "isa_nonalias_core_final", "isa_region_assume_core_final_v2"]]
    planned += [("base_core_final", "mapped_scorr_constants")]
    planned += [(name, "logic_scorr_prebalanced") for name in ["base_core_final", "isa_core_final", "isa_region_assume_core_final_v2", "isa_region_lemmas_core_final"]]
    statuses = {}
    for name, mode in planned:
        key = name + "/" + mode
        run = runs.get(key, {})
        stages = run.get("stages", [])
        first = stages[0] if stages else {}
        statuses[key] = {
            "outcome": "timeout" if first.get("status") == "timeout" else run.get("status", "not_started"),
            "runner_status": run.get("status", "not_started"),
            "optimization_seconds": first.get("elapsed_seconds"),
            "accepted_optimized_model": run.get("logic_complete", False),
            "result": str(root / key / "result.json"),
        }
    scorr_status = {
        "scope": "Ten prespecified whole-core monolithic correspondence attempts; timeout is not a proof of zero gain",
        "wall_limit_seconds_per_optimization": 3600,
        "runtime_environment": str(root / "runtime_environment.json"),
        "runtime_scope": "Concurrent shared-VM wall budgets, not isolated performance measurements",
        "trials": statuses,
        "counts": {state: sum(run["outcome"] == state for run in statuses.values()) for state in sorted({run["outcome"] for run in statuses.values()})},
        "accepted_optimized_models": sum(run["accepted_optimized_model"] for run in statuses.values()),
        "stopped_redundant_controls": {key: run["status"] for key, run in runs.items() if run.get("status") == "stopped_redundant_control"},
        "no_scorr_controls": {key: {field: run.get(field) for field in ["status", "logic_complete", "mapping_complete", "optimized", "stages"]} for key, run in runs.items() if not run.get("scorr", True)},
    }
    summary["formal_aig_core"]["status_summary"] = scorr_status
    (root / "whole_core_scorr_status.json").write_text(json.dumps(scorr_status, indent=2) + "\n")
    output = args.output or root / "whole_core_summary.json"
    output.write_text(json.dumps(summary, indent=2) + "\n")
    print(output)
    for family, members in [("physical_core", ["original", "region_cut"]), ("physical_core_modern_inprocess", ["original", "region_cut", "scheduler_cut", "combined_cut"]), ("physical_registerfile_capacity", ["guard64", "guard48"])]:
        print(family, "; ".join(name + "=" + summary[family][name]["status"] + ("/" + str(summary[family][name]["cell_area_um2"]) if "cell_area_um2" in summary[family][name] else "") for name in members))


if __name__ == "__main__":
    main()
