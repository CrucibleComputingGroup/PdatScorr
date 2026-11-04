#!/usr/bin/env python3
"""Prepare an isolated RSD Core synthesis run without changing upstream RTL.

The synthesis tail is imported from the existing Pscorr generator. This script
only adapts the SystemVerilog source list and optional explicit source patches.
It does not certify that an application meets an injected assumption.
"""
import argparse
import hashlib
import importlib.util
import json
import re
import shutil
import subprocess
from pathlib import Path


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("output", type=Path)
    p.add_argument("--core", type=Path, default=Path(__file__).resolve().parents[1] / "rsd")
    p.add_argument("--patches", type=Path, help="JSON list of {file, old, new}; every old must occur exactly once")
    p.add_argument("--isa-rv32i", action="store_true", help="Assume every valid predecoded instruction is RV32I class (including speculative instructions)")
    p.add_argument("--execution-regions", action="store_true", help="Assume every postreset executed load/store has physical address high bits zero/nonzero; no source comparator cuts")
    p.add_argument("--proven-region-invariants", action="store_true", help="Import the 32 finished-entry invariants certified by the actual LQ/SQ reset-based induction")
    p.add_argument("--lq", type=int, default=16)
    p.add_argument("--sq", type=int, default=16)
    p.add_argument("--mshr", type=int, default=2)
    p.add_argument("--frontend", choices=["synlig", "slang"], default="slang")
    p.add_argument("--no-implicit-memories", action="store_true")
    args = p.parse_args()
    if args.proven_region_invariants and (not args.execution_regions or args.lq != 16 or args.sq != 16):
        p.error("--proven-region-invariants requires --execution-regions and the proved 16-entry queue configuration")
    root = Path(__file__).resolve().parents[3]
    out = args.output.resolve()
    if out.exists():
        raise SystemExit(f"Refusing existing output directory: {out}")
    core = args.core.resolve()
    source = core / "Processor/Src"
    out.mkdir(parents=True)
    src = out / "src"
    shutil.copytree(source, src, ignore=shutil.ignore_patterns("obj_dir", "slpp_all", "*.log", "*.vcd"))
    config = src / "MicroArchConf.sv"
    config_text = config.read_text()
    for key, value in [("LOAD_QUEUE_ENTRY_NUM", args.lq), ("STORE_QUEUE_ENTRY_NUM", args.sq), ("DCACHE_MSHR_NUM", args.mshr)]:
        config_text, n = re.subn(r"(localparam CONF_" + key + r"\s*=\s*)\d+", lambda m: m[1] + str(value), config_text)
        assert n == 1, key
    config.write_text(config_text)
    applied = []
    if args.isa_rv32i:
        file = src / "Pipeline/PreDecodeStage.sv"
        body = """
    // Pscorr environment contract: includes wrong-path valid instructions.
    // Opcode classes form a conservative RV32I superset; OP excludes RV32M.
    for (genvar ps_lane = 0; ps_lane < DECODE_WIDTH; ps_lane++) begin
        wire [31:0] ps_insn = pipeReg[ps_lane].insn;
        always_comb begin
            if (!port.rst && pipeReg[ps_lane].valid)
                assume (
                    ps_insn[6:0] == 7'h03 || ps_insn[6:0] == 7'h23 ||
                    ps_insn[6:0] == 7'h13 || ps_insn[6:0] == 7'h37 ||
                    ps_insn[6:0] == 7'h17 || ps_insn[6:0] == 7'h63 ||
                    ps_insn[6:0] == 7'h67 || ps_insn[6:0] == 7'h6f ||
                    ps_insn[6:0] == 7'h0f || ps_insn[6:0] == 7'h73 ||
                    (ps_insn[6:0] == 7'h33 && ps_insn[31:25] != 7'h01)
                );
        end
    end
"""
        old = "endmodule : PreDecodeStage"
        text = file.read_text()
        assert text.count(old) == 1
        file.write_text(text.replace(old, body + "\n" + old))
        applied.append({"file": str(file.relative_to(src)), "kind": "valid-gated RV32I opcode-class superset"})
    if args.execution_regions:
        file = src / "Core.sv"
        body = """
    // Environment contract on every executed operation, including speculative
    // and invalid-register execution. No queue comparator is rewritten here.
    for (genvar ps_load_lane = 0; ps_load_lane < LOAD_ISSUE_WIDTH; ps_load_lane++) begin
        always_comb begin
            if (!rst && loadStoreUnitIF.executeLoad[ps_load_lane])
                assume (loadStoreUnitIF.executedLoadAddr[ps_load_lane][21:16] == 6'b0);
        end
    end
    for (genvar ps_store_lane = 0; ps_store_lane < STORE_ISSUE_WIDTH; ps_store_lane++) begin
        always_comb begin
            if (!rst && loadStoreUnitIF.executeStore[ps_store_lane])
                assume (loadStoreUnitIF.executedStoreAddr[ps_store_lane][21:16] != 6'b0);
        end
    end
"""
        text = file.read_text()
        assert text.count("endmodule : Core") == 1
        file.write_text(text.replace("endmodule : Core", body + "\nendmodule : Core"))
        applied.append({"file": "Core.sv", "kind": "postreset execution-region assumptions only, no comparator cuts"})
    proof_import = None
    if args.proven_region_invariants:
        formal = Path(__file__).resolve().parents[1] / "formal"
        proof_path = formal / "results/actual_lsq/summary.json"
        proof = json.loads(proof_path.read_text())
        if proof["status"] != "passed" or proof["property_counts"]["assert"] != 36:
            raise SystemExit("Actual RTL induction has not passed all required assertions")
        harness = formal / "LSQRegionProof.sv"
        if sha(harness) != proof["harness_sha256"]:
            raise SystemExit("Actual RTL proof harness has changed")
        for file, expected in proof["all_elaboration_source_sha256"].items():
            if sha(Path(file)) != expected:
                raise SystemExit(f"Proved RTL source changed: {file}")
        for name in ["base", "induction"]:
            if "Status: PASSED" not in (proof_path.parent / (name + ".log")).read_text():
                raise SystemExit(f"Missing successful actual RTL {name} proof")
        imported = []
        for module_name, array_name, count_name, relation in [
            ("LoadQueue", "loadQueue", "LOAD_QUEUE_ENTRY_NUM", "=="),
            ("StoreQueue", "storeQueue", "STORE_QUEUE_ENTRY_NUM", "!="),
        ]:
            relative = "LoadStoreUnit/" + module_name + ".sv"
            file = src / relative
            if sha(file) != proof["source_sha256"][relative]:
                raise SystemExit(f"Imported invariant requires original comparator RTL: {relative}")
            expression = f"!{array_name}[ps_entry].finished || {array_name}[ps_entry].address[19:14] {relation} 0"
            body = f"""
    // Imported actual-RTL inductive lemma. Its external justification requires
    // reset and the strict all-executed-operation address-region contract.
    // Keep all original queue logic and comparisons unchanged.
    for (genvar ps_entry = 0; ps_entry < {count_name}; ps_entry++) begin
        always_comb begin
            if (!port.rst)
                assume ({expression});
        end
    end
"""
            text = file.read_text()
            ending = "endmodule : " + module_name
            assert text.count(ending) == 1
            file.write_text(text.replace(ending, body + "\n" + ending))
            imported.append({"file": relative, "guard": "!port.rst", "expression": expression, "entries": 16, "original_sha256": proof["source_sha256"][relative]})
            applied.append({"file": relative, "kind": "proved finished-entry region invariant assumptions; original comparators retained"})
        proof_import = {
            "domain": "Reset-conditioned lemma-assisted specialization; original finished-entry facts follow from actual RTL induction under strict executed-operation region assumptions. Not arbitrary-initial-state equivalence.",
            "proof_summary": str(proof_path), "proof_summary_sha256": sha(proof_path),
            "harness": str(harness), "harness_sha256": sha(harness),
            "proof_artifacts_sha256": {name: sha(proof_path.parent / name) for name in ["base.log", "induction.log", "cover_nonvacuity.log", "model.smt2"]},
            "imported": imported,
        }
        (out / "proof_import.json").write_text(json.dumps(proof_import, indent=2) + "\n")
    if args.patches:
        for patch in json.loads(args.patches.read_text()):
            file = src / patch["file"]
            if not file.resolve().is_relative_to(src):
                raise SystemExit("Patch path outside source tree")
            text = file.read_text()
            if text.count(patch["old"]) != 1:
                raise SystemExit(f"Patch expected exactly one occurrence in {file}")
            file.write_text(text.replace(patch["old"], patch["new"]))
            applied.append(patch)
    mk = (src / "Makefiles/CoreSources.inc.mk").read_text()
    def files_for(name):
        m = re.search(r"^" + name + r"\s*=\s*\\\n((?:.*\\\n)*)", mk, re.M)
        if not m:
            raise SystemExit(f"Missing source variable {name}")
        return re.findall(r"\S+\.sv", m[1])
    files = files_for("TYPES") + files_for("CORE_MODULES")
    defines = ["RSD_SYNTHESIS", "RSD_SYNTHESIS_DESIGN_COMPILER", "REF=input", "RSD_DISABLE_DEBUG_REGISTER", "RSD_DISABLE_PERFORMANCE_COUNTER", "RSD_MARCH_INT_ISSUE_WIDTH=2", "RSD_MARCH_FP_PIPE", "RSD_ENABLE_ZBA", "RSD_ENABLE_ZICOND"]
    command = "read_slang --single-unit --top Core" if args.frontend == "slang" else "read_systemverilog -top Core"
    if args.no_implicit_memories:
        if args.frontend != "slang":
            raise SystemExit("--no-implicit-memories requires slang")
        command += " --no-implicit-memories"
    frontend = command + " -I" + str(src) + " " + " ".join("-D" + d for d in defines) + " " + " ".join(str(src / f) for f in files) + "\n"
    generator = root / "code/PdatProject/ScorrPdat/scripts/make_synthesis_script.py"
    module_spec = importlib.util.spec_from_file_location("pscorr_synthesis", generator)
    module = importlib.util.module_from_spec(module_spec)
    module_spec.loader.exec_module(module)
    common = "chformal -lower\nchformal -assert -remove\n" + module._generate_synthesis_commands("Core", str(out / "core"))
    common = common.replace("write_aiger -zinit", "write_verilog -noattr " + str(out / "rtl_logic.v") + "\nwrite_aiger -zinit")
    (out / "frontend.ys").write_text(frontend + "hierarchy -check -top Core\nwrite_rtlil " + str(out / "elaborated.il") + "\n")
    (out / "lower.ys").write_text("read_rtlil " + str(out / "elaborated.il") + "\n" + common)
    (out / "synth.ys").write_text(frontend + common)
    manifest = {
        "status": "prepared_not_run", "core_revision": subprocess.check_output(["git", "-C", str(core), "rev-parse", "HEAD"], text=True).strip(),
        "source_files": {f: sha(src / f) for f in files}, "defines": defines,
        "configuration": {"lq": args.lq, "sq": args.sq, "mshr": args.mshr},
        "patches": applied, "pscorr_generator": str(generator), "pscorr_generator_sha256": sha(generator),
        "proof_import": proof_import,
        "top": "Core", "frontend": args.frontend, "no_implicit_memories": args.no_implicit_memories, "observation": "Core top-level ports; debug/performance counters disabled in all variants", "memory_mapping": "All memories mapped to flip-flops by inherited Pscorr pipeline; not SRAM-macro area"
    }
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(out)


if __name__ == "__main__":
    main()
