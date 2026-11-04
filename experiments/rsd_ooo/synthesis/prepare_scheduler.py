#!/usr/bin/env python3
"""Prepare matched actual Scheduler/SelectLogic component synthesis."""
import argparse
import hashlib
import importlib.util
import json
import re
from pathlib import Path


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("variant", choices=["original", "nofp_cut", "dispatch_assume", "dispatch_lemmas"])
    parser.add_argument("output", type=Path)
    parser.add_argument("--mask-reset-outputs", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[3]
    experiment = root / "experiments/rsd_ooo"
    source = experiment / "rsd/Processor/Src"
    formal = experiment / "formal"
    candidate_dir = formal / "generated_scheduler_nofp"
    candidate_manifest = json.loads((candidate_dir / "candidate_manifest.json").read_text())
    proof = Path(candidate_manifest["proof_summary"])
    if sha(proof) != candidate_manifest["proof_summary_sha256"]:
        raise SystemExit("Scheduler proof summary changed")
    proof_data = json.loads(proof.read_text())
    if proof_data["status"] != "passed":
        raise SystemExit("Scheduler induction did not pass")
    files = (formal / "scheduler_sources.txt").read_text().splitlines()
    paths = []
    for file in files:
        path = source / file
        if sha(path) != proof_data["source_sha256"][file]:
            raise SystemExit(f"Proved source changed: {file}")
        if args.variant == "nofp_cut" and file == "Scheduler/Scheduler.sv":
            path = candidate_dir / "Scheduler.sv"
            if sha(path) != candidate_manifest["candidate_sha256"]:
                raise SystemExit("Scheduler candidate changed")
        paths.append(path)
    wrapper = formal / "SchedulerObserved.sv"
    out = args.output.resolve()
    if out.exists():
        raise SystemExit(f"Refusing existing output directory: {out}")
    out.mkdir(parents=True)
    wrapper_text = wrapper.read_text()
    masked_outputs = []
    if args.mask_reset_outputs:
        for line in wrapper_text.splitlines():
            match = re.match(r"\s*output\s+\w+\s+(?:\[[^\]]+\]\s*)*(.+)", line)
            if match:
                masked_outputs.extend(name.strip() for name in match[1].rstrip(",").split(","))
        assert len(masked_outputs) == 22 and all(re.fullmatch(r"\w+", name) for name in masked_outputs), masked_outputs
        marker = "        wakeup_stall = wakeup.stall;"
        assert wrapper_text.count(marker) == 1
        body = "\n        // Observe only outside reset; retain every internal reset transition.\n        if (rst) begin\n" + "".join("            " + name + " = '0;\n" for name in masked_outputs) + "        end"
        wrapper_text = wrapper_text.replace(marker, marker + body)
    if args.variant in ["dispatch_assume", "dispatch_lemmas"]:
        body = """
    for (genvar ps_lane = 0; ps_lane < DISPATCH_WIDTH; ps_lane++) begin
        always_comb begin
            if (!rst && writes[ps_lane])
                assume(port.writeSchedulerData[ps_lane].opType != MOP_TYPE_FP);
        end
    end
"""
        assert wrapper_text.count("endmodule") == 1
        wrapper_text = wrapper_text.replace("endmodule", body + "\nendmodule")
    proof_import = None
    if args.variant == "dispatch_lemmas":
        harness = formal / "SchedulerNoFPProof.sv"
        if sha(harness) != proof_data["harness_sha256"]:
            raise SystemExit("Scheduler proof harness changed")
        for name in ["contract_base.log", "contract_induction.log"]:
            if "Status: PASSED" not in (proof.parent / name).read_text():
                raise SystemExit(f"Missing successful proof: {name}")
        scheduler_source = source / "Scheduler/Scheduler.sv"
        scheduler_text = scheduler_source.read_text()
        expression = "!notIssued[ps_entry] || !isFP[ps_entry]"
        body = """
    // Actual-RTL proved invariant; valid after reset under every actual-write
    // no-FP admission contract. Original FP request logic remains unchanged.
    for (genvar ps_entry = 0; ps_entry < ISSUE_QUEUE_ENTRY_NUM; ps_entry++) begin
        always_comb begin
            if (!port.rst)
                assume(!notIssued[ps_entry] || !isFP[ps_entry]);
        end
    end
"""
        assert scheduler_text.count("endmodule : Scheduler") == 1
        imported_source = out / "Scheduler.sv"
        imported_source.write_text(scheduler_text.replace("endmodule : Scheduler", body + "\nendmodule : Scheduler"))
        paths[files.index("Scheduler/Scheduler.sv")] = imported_source
        proof_import = {
            "domain": "Reset-conditioned no-FP actual-write contract; original comparator/request logic retained",
            "guard": "!port.rst", "expression": expression, "entries": 16,
            "original_source_sha256": sha(scheduler_source),
            "proof_summary": str(proof), "proof_summary_sha256": sha(proof),
            "harness_sha256": sha(harness),
            "proof_artifacts_sha256": {name: sha(proof.parent / name) for name in ["contract_base.log", "contract_induction.log", "contract_cover.log", "contract.smt2"]},
        }
        (out / "proof_import.json").write_text(json.dumps(proof_import, indent=2) + "\n")
    (out / "SchedulerObserved.sv").write_text(wrapper_text)
    paths.append(out / "SchedulerObserved.sv")
    defines = ["RSD_SYNTHESIS", "RSD_SYNTHESIS_DESIGN_COMPILER", "REF=input", "RSD_DISABLE_DEBUG_REGISTER", "RSD_DISABLE_PERFORMANCE_COUNTER", "RSD_MARCH_INT_ISSUE_WIDTH=2", "RSD_MARCH_FP_PIPE", "RSD_ENABLE_ZBA", "RSD_ENABLE_ZICOND"]
    generator = root / "code/PdatProject/ScorrPdat/scripts/make_synthesis_script.py"
    spec = importlib.util.spec_from_file_location("pscorr_generator", generator)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    commands = module._generate_synthesis_commands("SchedulerObserved", str(out / "core"))
    commands = commands.replace("write_aiger -zinit", "write_verilog -noattr " + str(out / "rtl_logic.v") + "\nwrite_aiger -zinit")
    frontend = "read_slang --single-unit --top SchedulerObserved -I" + str(source) + " " + " ".join("-D" + d for d in defines) + " " + " ".join(map(str, paths)) + "\n"
    (out / "normalize.ys").write_text(frontend + "chformal -lower\nchformal -assert -remove\n" + commands)
    manifest = {
        "status": "prepared", "variant": args.variant,
        "scope": "Actual RSD Scheduler+SelectLogic component; all functional outputs retained, including raw pointers; no payload RAM or complete FP-unit removal claim",
        "capacity": "IQ16 and all original source parameters unchanged",
        "contract": candidate_manifest["contract"],
        "source_sha256": {str(path): sha(path) for path in paths},
        "defines": defines, "top": "SchedulerObserved",
        "candidate_manifest": str(candidate_dir / "candidate_manifest.json"),
        "candidate_manifest_sha256": sha(candidate_dir / "candidate_manifest.json"),
        "proof_summary": str(proof), "proof_summary_sha256": sha(proof),
        "generator_sha256": sha(generator),
        "reset_masked_outputs": masked_outputs,
        "proof_import": proof_import,
        "physical_mapping_input": "rtl_logic.v is before AIGER zinit; primary physical mapping must use it",
    }
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(out)


if __name__ == "__main__":
    main()
