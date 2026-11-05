#!/usr/bin/env python3
"""Prepare a pinned, capacity-preserving LEN5 integer baseline and elaborate it.

This is frontend qualification, not a Pscorr optimization or an area experiment.
The upstream checkout is read-only. All generated files go under --build.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import shlex
import subprocess
import time
from pathlib import Path

import yaml

PIN = "5206e92bc7235cd1cbcc10522aaee3f69f9b5e7b"
PRE_FPU_PIN = "14291dcc5bef181085d001c5a29e7f4fc4cbc8e9"
URL = "https://github.com/edge-group-polito/len5"
SWITCHES = ("LEN5_F_EN", "LEN5_D_EN", "LEN5_DUMMY_COPR_EN")
CORE_FILES = ("packages.core", "common.core", "frontend.core", "expipe.core", "datapath.core")
VENDOR_FILES = (
    "rtl/vendor/pulp-common-cells/src/cf_math_pkg.sv",
    "rtl/vendor/pulp-common-cells/src/lzc.sv",
    "rtl/vendor/pulp-common-cells/src/rr_arb_tree.sv",
)
INCLUDES = (
    "rtl/vendor/pulp-common-cells/include/common_cells/assertions.svh",
    "rtl/vendor/pulp-common-cells/include/common_cells/registers.svh",
)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git(repo: Path, *args: str) -> str:
    return subprocess.check_output(["git", "-C", str(repo), *args], text=True).strip()


def workspace_root(here: Path) -> Path:
    """Locate external tool/build storage when this script is in the code worktree."""
    return next((p for p in here.parents if (p / "tools/oss-cad-suite-20261104").exists()), here.parents[2])


def main() -> None:
    here = Path(__file__).resolve().parent
    workspace = workspace_root(here)
    external = workspace / "experiments/bounded_dynamic"
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--deps", type=Path, default=external / "deps" / "len5")
    parser.add_argument("--profile", choices=("current_integer", "pre_fpu"), default="current_integer")
    parser.add_argument("--build", type=Path)
    parser.add_argument("--yosys", type=Path, default=workspace / "tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys")
    parser.add_argument("--prepare-only", action="store_true")
    args = parser.parse_args()
    default_dir = "integer_frontend" if args.profile == "current_integer" else "pre_fpu_frontend"
    deps, build, yosys = args.deps.resolve(), (args.build or external / "len5/build" / default_dir).resolve(), args.yosys.resolve()
    revision = PIN if args.profile == "current_integer" else PRE_FPU_PIN
    switches = SWITCHES if args.profile == "current_integer" else ()
    includes = INCLUDES if args.profile == "current_integer" else ()
    def source_read(path: str) -> bytes:
        return subprocess.check_output(["git", "-C", str(deps), "show", revision + ":" + path])
    assert git(deps, "rev-parse", "HEAD") == PIN, "wrong LEN5 source pin"
    assert not git(deps, "status", "--porcelain"), "upstream checkout must be clean"
    assert yosys.is_file(), f"missing Yosys: {yosys}"
    build.mkdir(parents=True, exist_ok=True)
    source = build / "source"
    source.mkdir(exist_ok=True)

    # Follow the upstream RTL file order, omitting only uninstantiated optional
    # FP/coproc implementation dependencies. hierarchy -check rejects blackboxes.
    files: list[str] = []
    core_hashes = {}
    for core in CORE_FILES:
        path = deps / "rtl" / core
        raw = source_read(str(path.relative_to(deps)))
        core_hashes[str(path.relative_to(deps))] = digest(raw)
        doc = yaml.safe_load(raw)
        group = []
        for fs in doc["filesets"].values():
            if fs.get("file_type") != "systemVerilogSource":
                continue
            for f in fs.get("files", []):
                assert isinstance(f, str), (core, f)
                group.append("rtl/" + f)
        files.extend(group)
        if core == "packages.core" and args.profile == "current_integer":
            files.extend(VENDOR_FILES)
    assert len(files) == len(set(files)), "duplicate source files"

    original, prepared = {}, {}
    licenses = ["LICENSE"]
    if args.profile == "current_integer":
        licenses.append("rtl/vendor/pulp-common-cells/LICENSE")
    for f in [*files, *includes, *licenses]:
        raw = source_read(f)
        original[f] = digest(raw)
        if f == "rtl/packages/len5_config_pkg.sv":
            text = raw.decode()
            for name in switches:
                text, n = re.subn(rf"(localparam bit {name} = )1'b1;", rf"\g<1>1'b0;", text)
                assert n == 1, f"upstream switch changed: {name}"
            raw = text.encode()
        if f == "rtl/expipe/exec-units/exec_stage.sv" and args.profile == "current_integer":
            old_label = "end else begin : gen_no_div_unit\n      assign issue_ready_o[EU_DUMMY_COPR]"
            new_label = "end else begin : gen_no_copr_unit\n      assign issue_ready_o[EU_DUMMY_COPR]"
            text = raw.decode()
            assert text.count(old_label) == 1
            raw = text.replace(old_label, new_label).encode()
        p = source / f
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(raw)
        prepared[f] = digest(raw)

    config = (source / "rtl/packages/len5_config_pkg.sv").read_text()
    upstream_config = source_read("rtl/packages/len5_config_pkg.sv").decode()
    expected = upstream_config
    for name in switches:
        expected = expected.replace(f"localparam bit {name} = 1'b1;", f"localparam bit {name} = 1'b0;")
    assert expected == config, "unexpected baseline configuration edit"
    capacity_names = ("ROB_DEPTH", "IQ_DEPTH", "LDBUFF_DEPTH", "STBUFF_DEPTH", "ALU_RS_DEPTH", "MULT_RS_DEPTH", "DIV_RS_DEPTH", "BU_RS_DEPTH", "RAS_DEPTH")
    capacities = {name: int(re.search(rf"\b{name}\b[^=]*=\s*(?:32'd)?(\d+)", config).group(1)) for name in capacity_names}
    (build / "sources.txt").write_text("\n".join("source/" + f for f in files) + "\n")
    source_args = " ".join(shlex.quote("source/" + f) for f in files)
    include_args = "-I source/rtl/vendor/pulp-common-cells/include " if includes else ""
    script = (
        "read_slang --single-unit --no-implicit-memories --top datapath -D SYNTHESIS "
        + include_args + source_args + "\n"
        "hierarchy -check -top datapath\n"
        "stat\n"
        "write_rtlil elaborated.il\n"
    )
    (build / "frontend.ys").write_text(script)
    manifest = {
        "purpose": "Frontend qualification only; no optimization, capacity sweep, physical-area claim, or correctness proof",
        "upstream_url": URL, "upstream_commit": revision, "upstream_checkout_commit": PIN,
        "upstream_clean": True, "profile": args.profile,
        "top": "datapath", "top_parameters": {"FETCH_MEMIF_FIFO_DEPTH": 2, "BOOT_PC": 0},
        "baseline_switches": {x: {"upstream": 1, "baseline": 0} for x in switches},
        "compatibility_edits": ([{"path": "rtl/expipe/exec-units/exec_stage.sv", "change": "Rename the disabled-coprocessor generate block gen_no_div_unit to gen_no_copr_unit; original duplicates the divider block name", "logic_change": False}] if args.profile == "current_integer" else []),
        "capacity_parameters_unchanged": capacities,
        "original_sha256": original, "prepared_sha256": prepared,
        "upstream_core_manifest_sha256": core_hashes,
        "source_count": len(files), "source_lines": sum(len((source / f).read_text().splitlines()) for f in files),
        "yosys": str(yosys), "yosys_sha256": digest(yosys.read_bytes()),
        "yosys_version": subprocess.check_output([str(yosys), "-V"], text=True).strip(),
        "frontend_script_sha256": digest(script.encode()),
        "command": [str(yosys), "-m", "slang", "-Q", "-T", "-s", "frontend.ys"],
        "status": "prepared",
        "dependency_note": "Python3 + PyYAML + Yosys slang plugin. All selected RTL is pinned in upstream git objects; no FuseSoC installation needed for this explicit RTL source list.",
    }
    if not args.prepare_only:
        start = time.monotonic()
        with (build / "frontend.log").open("w") as log:
            p = subprocess.run(manifest["command"], cwd=build, stdout=log, stderr=subprocess.STDOUT)
        manifest.update(returncode=p.returncode, elapsed_seconds=time.monotonic() - start,
                        status="elaborated" if p.returncode == 0 else "frontend_failed")
        if p.returncode == 0:
            manifest["elaborated_il_sha256"] = digest((build / "elaborated.il").read_bytes())
            check_script = "read_rtlil elaborated.il\ncheck -assert\n"
            (build / "check.ys").write_text(check_script)
            check_command = [str(yosys), "-Q", "-T", "-s", "check.ys"]
            with (build / "check.log").open("w") as log:
                check = subprocess.run(check_command, cwd=build, stdout=log, stderr=subprocess.STDOUT)
            check_text = (build / "check.log").read_text()
            manifest["structural_check"] = {
                "command": check_command, "returncode": check.returncode,
                "log_sha256": digest(check_text.encode()),
                "warnings": [x for x in check_text.splitlines() if x.startswith("Warning:")],
            }
            if check.returncode:
                manifest["status"] = "elaborated_with_structural_issues"
            if args.profile == "pre_fpu":
                # The official pre-FPU RTL assigns load mem_we_o=0 twice.
                # Standard constant/alias cleanup resolves identical drivers;
                # retain the raw check above instead of hiding its diagnostic.
                normalize_script = (
                    "read_rtlil elaborated.il\nopt_expr\nopt_clean\n"
                    "check -assert\nstat\nwrite_rtlil normalized.il\n"
                )
                (build / "normalize.ys").write_text(normalize_script)
                normalize_command = [str(yosys), "-Q", "-T", "-s", "normalize.ys"]
                with (build / "normalize.log").open("w") as log:
                    norm = subprocess.run(normalize_command, cwd=build, stdout=log, stderr=subprocess.STDOUT)
                manifest["normalized_structural_check"] = {
                    "command": normalize_command, "returncode": norm.returncode,
                    "script_sha256": digest(normalize_script.encode()),
                    "log_sha256": digest((build / "normalize.log").read_bytes()),
                    "rtl_source_edits": False,
                }
                if norm.returncode == 0:
                    manifest["normalized_il_sha256"] = digest((build / "normalized.il").read_bytes())
                    manifest["status"] = "normalized_structural_check_passed"
                else:
                    manifest["status"] = "normalized_structural_check_failed"
        manifest["frontend_log_sha256"] = digest((build / "frontend.log").read_bytes())
    assert not git(deps, "status", "--porcelain"), "upstream checkout mutated"
    (build / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps({k: manifest[k] for k in ("status", "source_count", "capacity_parameters_unchanged")}))
    if manifest.get("returncode", 0):
        raise SystemExit(manifest["returncode"])
    if manifest.get("normalized_structural_check", {}).get("returncode", 0):
        raise SystemExit(manifest["normalized_structural_check"]["returncode"])
    if not manifest.get("normalized_structural_check") and manifest.get("structural_check", {}).get("returncode", 0):
        raise SystemExit(manifest["structural_check"]["returncode"])


if __name__ == "__main__":
    main()
