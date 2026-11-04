#!/usr/bin/env python3
"""Prepare matched guarded 64/48-register component area controls."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("simulation_variant", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[3]
    formal = root / "experiments/rsd_ooo/formal"
    variant = args.simulation_variant.resolve()
    source = variant / "source/Processor/Src"
    inherited = json.loads((variant / "manifest.json").read_text())
    assert inherited["prf_reset_guard"] is True
    files = (formal / "registerfile_sources.txt").read_text().splitlines()
    paths = [source / file for file in files]
    for file, path in zip(files, paths):
        if sha(path) != inherited["source_sha256"][file]:
            raise SystemExit(f"Simulation source changed: {file}")
    out = args.output.resolve()
    if out.exists():
        raise SystemExit(f"Refusing existing output directory: {out}")
    out.mkdir(parents=True)
    wrapper = out / "RegisterFileObserved.sv"
    wrapper.write_bytes((formal / "RegisterFileObserved.sv").read_bytes())
    paths.append(wrapper)
    defines = ["RSD_SYNTHESIS", "RSD_SYNTHESIS_DESIGN_COMPILER", "REF=input", "RSD_DISABLE_DEBUG_REGISTER", "RSD_DISABLE_PERFORMANCE_COUNTER", "RSD_MARCH_INT_ISSUE_WIDTH=2", "RSD_MARCH_FP_PIPE", "RSD_ENABLE_ZBA", "RSD_ENABLE_ZICOND"]
    generator = root / "code/PdatProject/ScorrPdat/scripts/make_synthesis_script.py"
    spec = importlib.util.spec_from_file_location("pscorr_generator", generator)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    commands = module._generate_synthesis_commands("RegisterFileObserved", str(out / "core"))
    # Primary result is normalized physical RTL, with no zinit conversion.
    commands = "\n".join(line for line in commands.splitlines() if not line.lstrip().startswith("write_aiger"))
    commands += "\nwrite_verilog -noattr " + str(out / "rtl_logic.v") + "\n"
    frontend = "read_slang --single-unit --top RegisterFileObserved -I" + str(source) + " " + " ".join("-D" + define for define in defines) + " " + " ".join(map(str, paths)) + "\n"
    (out / "normalize.ys").write_text(frontend + "chformal -lower\nchformal -assert -remove\n" + commands)
    manifest = {
        "status": "prepared", "scope": "RegisterFile component, all functional read/write ports and data-valid bits; separate complex pipeline and FP bank enabled; flop-mapped storage",
        "interpretation": "Capacity/performance control with explicit common reset compatibility guard; NOT Pscorr pruning or unrestricted-address equivalence",
        "integer_physical_registers": inherited["integer_physical_registers"],
        "fp_physical_registers": inherited["fp_physical_registers"],
        "reset_guard_scope": inherited["prf_reset_guard_scope"],
        "simulation_variant_manifest": str(variant / "manifest.json"), "simulation_manifest_sha256": sha(variant / "manifest.json"),
        "source_sha256": {str(path): sha(path) for path in paths},
        "included_macros_sha256": sha(source / "BasicMacros.sv"),
        "wrapper_sha256": sha(wrapper), "defines": defines,
        "generator_sha256": sha(generator), "initialization": "Normalized RTL before AIGER; no zinit encoding",
    }
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(out)


if __name__ == "__main__":
    main()
