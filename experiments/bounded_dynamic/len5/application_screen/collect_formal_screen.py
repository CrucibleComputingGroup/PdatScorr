#!/usr/bin/env python3
"""Collect and independently verify compact admission-screen review evidence.

Reads existing runs only. No solver, simulator, synthesis or optimization is run.
Large models are hash-bound; a gzip AIG is included only when a witness exists.
"""
from __future__ import annotations
import argparse
import copy
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from prepare_frontend import PRE_FPU_PIN, workspace_root


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n")


def main():
    workspace = workspace_root(HERE)
    root = workspace / "experiments/bounded_dynamic/len5/build"
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", type=Path, default=root / "streaming_alphabet_gap2_v5_alu_mul")
    parser.add_argument("--output", type=Path, default=HERE / "evidence/formal_screen_v5")
    args = parser.parse_args()
    src, out = args.build.resolve(), args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    frontend = root / "pre_fpu_frontend"
    fm = json.loads((frontend / "manifest.json").read_text())
    summary = json.loads((src / "summary.json").read_text())
    assert summary["source_commit"] == fm["upstream_commit"] == PRE_FPU_PIN
    assert fm["prepared_sha256"] == fm["original_sha256"]
    assert digest(frontend / "normalized.il") == fm["normalized_il_sha256"] == summary["source_rtlil_sha256"]
    deps = workspace / "experiments/bounded_dynamic/deps/len5"
    source_audit = {}
    for rel, expected in fm["prepared_sha256"].items():
        raw = subprocess.check_output(["git", "-C", str(deps), "show", PRE_FPU_PIN + ":" + rel])
        assert hashlib.sha256(raw).hexdigest() == expected == digest(frontend / "source" / rel), rel
        source_audit[rel] = expected
    for key, name in (("source_json", "source.json"), ("core_json", "core.json"),
                      ("core", "core.v"), ("script", "formal_screen.py"),
                      ("harness", "AdmissionScreen.sv"), ("aig", "screen.aig"),
                      ("abstraction_helper", "abstract_datapath.py")):
        assert digest(src / name) == summary[key + "_sha256"], name
    assert summary["abstraction_mode"] == "alu_mul" and summary["accepted_optimization"] is False
    assert summary["status"] == "unknown"
    assert summary["nonfaulting_response_code"] == 31 and summary["invalid_response_codes"] == [0, 31]
    for key in ("source_export", "prepare", "export", "pdr"):
        run = summary[key]
        assert digest(run["log"]) == run["log_sha256"], key
        assert digest(run["executable"]) == run["executable_sha256"], key
        assert run["returncode"] == 0 and not run["timeout"], key
    pdr = (src / "pdr.log").read_text()
    assert "Property UNDECIDED." in pdr and "Reached timeout (120 seconds) in frame 8." in pdr
    assert "was asserted" not in pdr and "Property proved." not in pdr

    # Reconstruct exactly the two-driver abstraction from its frozen helper.
    spec = importlib.util.spec_from_file_location("frozen_abstract", src / "abstract_datapath.py")
    helper = importlib.util.module_from_spec(spec); spec.loader.exec_module(helper)
    original = json.loads((src / "source.json").read_text())
    recreated, audit = helper.abstract_datapath(original, "datapath", mode="alu_mul")
    assert audit == json.loads((src / "abstraction.json").read_text()) == summary["datapath_abstraction"]
    observed = json.loads((src / "core.json").read_text())
    mod = observed["modules"]["datapath"]
    for alias, target in (("probe_insert", "insert"), ("probe_index", "new_idx")):
        assert mod["ports"].pop(alias) == {"direction": "output", "bits": mod["netnames"][
            "u_backend.u_exec_stage.u_alu_unit.u_arith_rs." + target]["bits"]}
    assert observed == recreated, "Unexpected source/cell/port changes outside exact cuts and probes"
    assert sum(c["type"] == "$anyseq" for c in mod["cells"].values()) == 2
    assert audit["fresh_symbolic_bits_per_cycle"] == 128
    prep = (src / "prepare.ys").read_text()
    assert 'read_json ' in prep and 'core.json' in prep and not re.search(r"read_verilog[^\n]*core\.v", prep)
    screen = json.loads((src / "screen.json").read_text())["modules"]["AdmissionScreen"]
    assert sum(c["type"] == "$assert" for c in screen["cells"].values()) == 3
    assert sum(c["type"] == "$anyseq" for c in screen["cells"].values()) == 2
    assertion_inventory = [{"cell": n, "source": c["attributes"].get("src"),
        "connections": c["connections"]} for n, c in screen["cells"].items() if c["type"] == "$assert"]
    assert sum(a["connections"]["A"] == ["1"] for a in assertion_inventory) == 2
    nonconstant = [a for a in assertion_inventory if a["connections"]["A"] != ["1"]]
    assert len(nonconstant) == 1 and "AdmissionScreen.sv:122." in nonconstant[0]["source"]
    with (src / "screen.aig").open("rb") as f:
        header = f.readline().decode().split()
        assert header == summary["aig_header"] and int(header[4]) == 0
        for _ in range(int(header[3])): f.readline()
        bad_literals = [f.readline().decode().strip() for _ in range(int(header[6]))]
        constraint_literals = [f.readline().decode().strip() for _ in range(int(header[7]))]

    copied = {}
    def collect(path, rel):
        if path.suffix == ".log" and path.stat().st_size > 128 * 1024:
            rel += ".gz"
            dest = out / rel; dest.parent.mkdir(parents=True, exist_ok=True)
            with dest.open("wb") as raw:
                with gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as stream:
                    stream.write(path.read_bytes())
            assert hashlib.sha256(gzip.decompress(dest.read_bytes())).hexdigest() == digest(path)
            copied[rel] = {"original_path": str(path), "sha256": digest(dest), "bytes": dest.stat().st_size,
                           "decompressed_sha256": digest(path)}
            return
        dest = out / rel; dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, dest)
        assert digest(dest) == digest(path)
        copied[rel] = {"original_path": str(path), "sha256": digest(dest), "bytes": dest.stat().st_size}
    names = ("formal_screen.py", "abstract_datapath.py", "AdmissionScreen.sv", "abstraction.json", "summary.json",
             "source_export.ys", "source_export.log", "core_export.ys", "core_export.log", "prepare.ys", "prepare.log",
             "export.ys", "export.log", "pdr.log")
    for name in names: collect(src / name, "v5/" + name)
    for name in ("manifest.json", "frontend.ys", "normalize.ys", "sources.txt"):
        collect(frontend / name, "source_binding/" + name)
    collect(frontend / "source/LICENSE", "source_binding/LICENSE")
    for name in ("formal_screen_review.md", "formal_screen_v3_trace_audit.json"):
        collect(HERE / name, "review/" + name)
    for name in ("program.disasm", "program.S", "platform_timing_summary.json"):
        collect(HERE.parent / "results/streaming_fetchgap2_v2" / name, "inputs/" + name)
    words = [w.lower() for a, w in re.findall(r"(?m)^\s*([0-9a-f]+):\s+([0-9a-f]{8})\s",
        (out / "inputs/program.disasm").read_text()) if int(a, 16) < 0x38]
    assert words == summary["instruction_alphabet"] and len(words) == 14
    history = []
    for version, dirname in (("v1", "streaming_alphabet_gap2_v1"), ("v2", "streaming_alphabet_gap2_v2"),
                             ("v3", "streaming_alphabet_gap2_v3"), ("v4", "streaming_alphabet_gap2_v4_alu_mul")):
        previous = root / dirname
        old = json.loads((previous / "summary.json").read_text())
        for name in ("summary.json", "formal_screen.py", "AdmissionScreen.sv", "prepare.ys", "prepare.log",
                     "export.ys", "export.log", "pdr.log"):
            if (previous / name).is_file(): collect(previous / name, "history/" + version + "/" + name)
        for key, name in (("script", "formal_screen.py"), ("harness", "AdmissionScreen.sv")):
            assert digest(previous / name) == old[key + "_sha256"]
        if "aig_sha256" in old: assert digest(previous / "screen.aig") == old["aig_sha256"]
        history.append({"version": version, "original_path": str(previous), "status": old["status"],
                        "error": old.get("error"), "accepted_optimization": old["accepted_optimization"]})

    bounded = {"status": "pending", "accepted_optimization": False,
               "scope": "Bounded diagnostic only, never unbounded safety or native implementation acceptance"}
    bdir = src / "bounded_screen"
    if (bdir / "summary.json").exists():
        bs = json.loads((bdir / "summary.json").read_text())
        assert bs["aig_sha256"] == summary["aig_sha256"]
        assert digest(bdir / "bmc.log") == bs["run"]["log_sha256"]
        assert digest(bs["run"]["executable"]) == bs["run"]["executable_sha256"]
        log = (bdir / "bmc.log").read_text()
        cex = re.search(r"Output (\d+) of miter .* was asserted in frame (\d+)", log)
        for name in ("summary.json", "bmc.log"):
            collect(bdir / name, "v5/bounded_screen/" + name)
        bounded.update(status="abstract_counterexample" if cex else "unknown_or_bounded_only",
                       merged_output=int(cex[1]) if cex else None, frame=int(cex[2]) if cex else None,
                       concretization="unresolved", original_summary_sha256=digest(bdir / "summary.json"))
        if cex:
            bounded["violated_property"] = "ALU admission prohibition at harness line122: both readiness assertions have literal A=1 in screen.json"
        if (bdir / "validation_execution.json").exists():
            validation = json.loads((bdir / "validation_execution.json").read_text())
            assert validation["returncode"] == 0 and not validation["timeout"]
            assert digest(bdir / "validate.log") == validation["log_sha256"]
            assert digest(validation["executable"]) == validation["executable_sha256"]
            vtext = (bdir / "validate.log").read_text()
            assert "Counter-example verification succeeded." in vtext and "Main AIG: The cex is correct." in vtext
            for name in ("validation_execution.json", "validate.log"):
                collect(bdir / name, "v5/bounded_screen/" + name)
            bounded["abc_witness_validation"] = "passed on the same folded/orpos abstract AIG; native concretization unresolved"
        if (bdir / "counterexample.aiw").exists():
            collect(bdir / "counterexample.aiw", "v5/bounded_screen/counterexample.aiw")
            # Exact AIG/symbol ordering is needed to interpret this witness.
            gz = out / "v5/screen.aig.gz"
            with gz.open("wb") as raw:
                with gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as stream:
                    stream.write((src / "screen.aig").read_bytes())
            assert hashlib.sha256(gzip.decompress(gz.read_bytes())).hexdigest() == summary["aig_sha256"]
            copied["v5/screen.aig.gz"] = {"original_path": str(src / "screen.aig"), "sha256": digest(gz),
                "bytes": gz.stat().st_size, "decompressed_sha256": summary["aig_sha256"],
                "reason_retained": "Exact witness model and AIG symbols; proof abstraction, not native hardware"}
    else:
        bounded["reason"] = "Run summary absent at collection; do not interpret partial log as a completed result"

    large = {}
    for name in ("source.json", "core.json", "core.v", "screen.json", "screen.aig"):
        path = src / name
        large[name] = {"original_path": str(path), "sha256": digest(path), "bytes": path.stat().st_size,
                       "retained": name == "screen.aig" and (out / "v5/screen.aig.gz").exists()}
    named = src / "bounded_screen/counterexample.named.txt"
    if named.exists():
        large["bounded_screen/counterexample.named.txt"] = {"original_path": str(named),
            "sha256": digest(named), "bytes": named.stat().st_size, "retained": False,
            "reproduction": "ABC write_cex -n -c after read_aiger; fold; orpos; read_cex; testcex -a (exact command in validation_execution.json)"}
    # These dependency snapshots are reviewed now; the original run did not
    # individually record their Python hashes. Exact generated tool scripts,
    # executable hashes and input/output model hashes provide the run binding.
    repo = HERE.parents[3]
    for path, rel in ((repo / "odc/temporal.py", "dependencies/temporal.py"),
                      (HERE.parent / "prepare_frontend.py", "dependencies/prepare_frontend.py"),
                      (Path(__file__), "dependencies/collect_formal_screen.py")):
        collect(path, rel)
    provenance = {"scope": "Reviewed proof-only admission screen; NO accepted optimization, hardware candidate, area or performance gain",
        "source_commit": PRE_FPU_PIN, "source_url": "https://github.com/edge-group-polito/len5/tree/" + PRE_FPU_PIN,
        "source_binding": {"all_prepared_files_verified_against_pinned_git_objects": True,
            "file_count_including_license": len(source_audit), "source_sha256": source_audit,
            "normalized_rtlil_sha256": summary["source_rtlil_sha256"],
            "reconstructed_abstraction_and_probes_exact": True, "native_capacities": fm["capacity_parameters_unchanged"]},
        "v5": {"pdr_status": "unknown", "pdr_timeout_frame": 8, "accepted_optimization": False,
            "abstraction_mode": "alu_mul", "symbolic_payload_bits": 128,
            "correct_nonfaulting_code": 31, "invalid_codes_allowed": [0, 31],
            "aig_header": header, "bad_literals": bad_literals, "constraint_literals": constraint_literals,
            "assertion_inventory": assertion_inventory,
            "bounded": bounded}, "history": history, "large_artifacts": large,
        "copied_files": copied,
        "rom_scope_limit": "The data abstraction includes all behaviors of the original core under the same instruction-alphabet/platform environment. Finite trace audit shows every returned padded-kernel fetch is in that alphabet. No unbounded theorem excludes fetches of other padding/data words in the actual ROM; the frozen runner docstring's ROM-overapproximation wording must be read with this limitation.",
        "dependency_provenance_limit": "Runner/helper snapshots are runtime hash-bound. temporal.py and prepare_frontend.py snapshots are collection-time references; their historical Python hashes were not individually recorded by the runner. Exact executed Yosys scripts/logs, binary hashes, source/core/AIG hashes and independently reconstructed cuts are verified.",
        "collector_sha256": digest(__file__)}
    write(out / "PROVENANCE.json", provenance)
    text = """# Formal admission-screen evidence (v5)

**No optimization is accepted.** The original-core v3 query reached PDR frame7
and timed out; the v5 proof abstraction reached frame8 and timed out. v5 replaces
only two 64-bit combinational ALU/MUL result drivers with symbolic values.
This admits all original traces plus extra behaviors; it is not native hardware
and its cone/state counts are not area savings.

@BOUNDED_OUTCOME@

Version history: v1/v2 used a queue-age instruction service that did not match
native readiness/flush behavior; v1 also failed residual-memory validation and
v2 stopped in ABC export. v3 corrected the fetch handshake but used0 instead of
native31 for successful response exception codes. v4 corrected codes/source
binding and introduced proof-only ALU/MUL abstraction, but Verilog rereading
failed on `$anyseq`. v5 reads the core JSON directly, preserving those symbols.
No failed, timed-out or bounded-only run is treated as proof.

The v3 trace audit and source review are under review/. v5's source manifest,
original pin, exact cuts, scripts, harness, logs and hashes are retained. Large
JSON/Verilog models remain external with hashes in PROVENANCE.json. When a
witness exists, v5/screen.aig.gz retains its exact AIG and symbol order; decompress
before using it. Large text logs are retained losslessly as .log.gz. The large
named witness listing remains external with its hash and regeneration command;
the machine AIW and validation records are included. The instruction alphabet is independently checked against the
included padded-kernel disassembly. Source files are verified against upstream
git objects at the exact pinned revision.

The sound data-abstraction relation is under the same **instruction-alphabet
environment**. Recorded kernel fetches all belong to that alphabet, but no
unbounded theorem excludes other padding/data words from the actual ROM.
The frozen runner's general ROM-overapproximation wording exceeds that evidence;
this package establishes finite trace inclusion and alphabet-domain screening.

Reproduction from the code-repository root (fresh output paths):

```sh
python3 experiments/bounded_dynamic/len5/prepare_frontend.py --profile pre_fpu
python3 experiments/bounded_dynamic/len5/application_screen/formal_screen.py \\
  --disassembly experiments/bounded_dynamic/len5/application_screen/evidence/formal_screen_v5/inputs/program.disasm \\
  --output /tmp/len5-admission-review --gap 2 --threshold 4 \\
  --datapath-abstraction alu_mul --timeout 120
```

Verify the current runner/helper hashes against v5/ before reproduction. The
PDR and bounded ABC command lines are recorded verbatim in their run summaries.
Tool versions are bound by executable hashes. Collect this review into a fresh
directory with `application_screen/collect_formal_screen.py --output PATH`.
The collector does not run experiments. SHA256SUMS covers every package file
except itself; PROVENANCE.json distinguishes original-run and review-time hashes.
"""
    if bounded["status"] == "abstract_counterexample":
        outcome = (f"The bounded diagnostic found an abstract ALU admission violation at frame {bounded['frame']}. "
            "Both readiness assertions are constant true in the prepared model, leaving only the ALU admission prohibition. "
            "ABC validated the retained witness on the same abstract AIG. Native-core concretization remains unresolved; "
            "this is not a native occupancy counterexample. See PROVENANCE.json and v5/bounded_screen/.")
    else:
        outcome = f"Bounded diagnostic status: {bounded['status']}. No completed unbounded safety result or native implementation acceptance follows."
    text = text.replace("@BOUNDED_OUTCOME@", outcome)
    (out / "README.md").write_text(text)
    paths = sorted(p for p in out.rglob("*") if p.is_file())
    (out / "SHA256SUMS").write_text("".join(f"{digest(p)}  {p.relative_to(out)}\n" for p in paths))
    print(json.dumps({"output": str(out), "files": len(paths) + 1,
                      "bytes": sum(p.stat().st_size for p in out.rglob("*") if p.is_file()),
                      "pdr": "unknown", "bounded": bounded, "accepted_optimization": False}, indent=2))


if __name__ == "__main__":
    main()
