#!/usr/bin/env python3
"""Run unchanged LEN5 with ELF-derived, separate instruction and data images."""
from __future__ import annotations
import argparse
import csv
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE.parent / "application_screen"))
from prepare_frontend import PRE_FPU_PIN, digest, workspace_root
from run_div_falsifier import extract
from run_streaming import stores
from analyze_fetch_spacing import native_edges, timing, dynamic_issue
from elf_images import executable_images, read_hex, write_hex

MASK = (1 << 64) - 1
INPUT = [((i * 0x9e3779b97f4a7c15) ^ (i << 17)) & MASK for i in range(64)]


def csv_write(path, rows):
    assert rows
    with path.open("w") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0])); writer.writeheader(); writer.writerows(rows)


def main():
    external = workspace_root(HERE) / "experiments/bounded_dynamic/len5/build"
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--simulator-build", type=Path, default=external / "harvard_gap2_platform_v1")
    ap.add_argument("--reference-image", type=Path, default=external / "streaming_fetchgap2_v2/program.hex")
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--evidence", type=Path, required=True)
    args = ap.parse_args()
    build, out, evidence = args.simulator_build.resolve(), args.output.resolve(), args.evidence.resolve()
    manifest = json.loads((build / "manifest.json").read_text())
    binary = build / "obj_dir/Vtb_bare"
    assert manifest["upstream_commit"] == PRE_FPU_PIN and manifest["build_returncode"] == 0
    assert manifest["core_rtl_source_edits"] is False and manifest["fetch_fifo_depth"] == 2
    assert manifest["instruction_min_accept_spacing"] == 2 and manifest["memory_pipe_num"] == 2
    assert manifest["instruction_memory_platform"] == "separate_immutable_elf_executable_rom"
    assert digest(binary.read_bytes()) == manifest["binary_sha256"]
    for name, expected in manifest["harvard_source_sha256"].items():
        assert digest((HERE / name).read_bytes()) == expected
    out.mkdir(parents=True, exist_ok=False); evidence.mkdir(parents=True, exist_ok=False)
    source_files = [Path(__file__), HERE / "streaming.S", HERE / "platform.ld", HERE / "elf_images.py",
                    HERE / "platform_patch.py", HERE / "harvard_lookup.svh", HERE.parent / "qualify_simulation.py",
                    HERE.parent / "application_screen/run_streaming.py",
                    HERE.parent / "application_screen/analyze_fetch_spacing.py", HERE.parent / "run_div_falsifier.py"]
    source_hashes = {str(p): digest(p.read_bytes()) for p in source_files}
    for p in source_files: shutil.copyfile(p, out / p.name)
    (out / "input.bin").write_bytes(b"".join(x.to_bytes(8, "little") for x in INPUT))
    env = {**os.environ, "PATH": "/usr/bin:/bin:/usr/local/bin"}
    commands = [
        ["riscv64-linux-gnu-gcc", "-march=rv64im", "-mabi=lp64", "-nostdlib", "-static",
         "-Wl,-T,platform.ld", "-Wl,--build-id=none", "streaming.S", "-o", "program.elf"],
        ["riscv64-linux-gnu-objcopy", "-O", "binary", "--only-section=.text", "program.elf", "text.bin"],
        ["riscv64-linux-gnu-objcopy", "-O", "binary", "--only-section=.rodata", "program.elf", "rodata.bin"],
    ]
    with (out / "compile.log").open("w") as f:
        for command in commands: subprocess.run(command, cwd=out, env=env, stdout=f, stderr=subprocess.STDOUT, check=True)
    for command, name in [(["riscv64-linux-gnu-objdump", "-d", "program.elf"], "program.disasm"),
                          (["riscv64-linux-gnu-readelf", "-W", "-l", "-S", "program.elf"], "program.readelf")]:
        with (out / name).open("w") as f: subprocess.run(command, cwd=out, env=env, stdout=f, check=True)
    instruction, ram, image_record = executable_images(out / "program.elf")
    assert set(instruction) == set(range(56)) and set(ram) == set(range(0x1000, 0x1280))
    text = bytes(instruction[i] for i in range(56))
    data = bytes(ram[i] for i in range(0x1000, 0x1280))
    assert text == (out / "text.bin").read_bytes() and data == (out / "rodata.bin").read_bytes()
    reference = read_hex(args.reference_image)
    assert all(reference[k] == v for k, v in instruction.items())
    assert data == (out / "input.bin").read_bytes() + bytes(128)
    write_hex(out / "instruction.hex", instruction); write_hex(out / "data.hex", ram)
    image_record.update(instruction_byte_count=len(instruction), data_byte_count=len(ram),
        instruction_words=[{"address": i, "word": f"{int.from_bytes(text[i:i+4], 'little'):08x}"} for i in range(0, 56, 4)],
        reference_image_sha256=digest(args.reference_image.read_bytes()),
        original_56_instruction_bytes_identical=True, independent_objcopy_sections_match=True,
        instruction_hex_sha256=digest((out / "instruction.hex").read_bytes()),
        data_hex_sha256=digest((out / "data.hex").read_bytes()),
        instruction_data_address_sets_disjoint=True,
        data_layout={"input_address": 4096, "input_bytes": 512, "padding_address": 4608, "padding_zero_bytes": 128})
    (out / "elf_image_manifest.json").write_text(json.dumps(image_record, indent=2) + "\n")
    run = [str(binary), "+firmware=" + str(out / "data.hex"), "+instruction_rom=" + str(out / "instruction.hex"),
           "--max_cycles=10000", "--dump_waves=true", "--dump_trace=true", "--log_level=LOG_LOW"]
    with (out / "run.log").open("w") as f:
        proc = subprocess.run(run, cwd=out, env=env, stdout=f, stderr=subprocess.STDOUT, timeout=60)
    log = (out / "run.log").read_text()
    exit_ok = (proc.returncode == 0 and "Program exit with code: 0x00 (SUCCESS)" in log
               and "Simulation completed successfully" in log
               and not any(x in log for x in ["ERROR", "FAILURE"]) and "timeout" not in log.lower())
    subprocess.run(["/usr/bin/fst2vcd", str(out / "logs/waves.fst"), "-o", str(out / "all.vcd")], check=True, capture_output=True)
    occupancy = extract(out / "all.vcd", evidence / "rs_state.vcd", evidence / "occupancy.csv")
    writes = stores(out / "all.vcd")
    expected = [{"data_store_addr_o": 0x2000 + i*8, "data_store_wdata_o": (x + 1) & MASK,
                 "data_store_be_o": 255} for i, x in enumerate(INPUT)]
    expected.append({"data_store_addr_o": 0x20000100, "data_store_wdata_o": 0, "data_store_be_o": 1})
    observed = [{k: v for k, v in row.items() if k != "time"} for row in writes]
    stores_ok = observed == expected
    rows = native_edges(out / "all.vcd", {"fetch_response_word": "TOP.tb_bare.u_datapath.instr_rdata_i"})
    service, fetches, loads = timing(rows, 2)
    issue = dynamic_issue(out / "logs/qualification_events.csv")
    # Check every returned instruction payload, including invalid/speculative cycles.
    words = {int(x["word"], 16) for x in image_record["instruction_words"]}
    assert all(r["fetch_response_word"] in words | {0} for r in rows if r["reset_n"])
    assert all(r["fetch_response_word"] == 0 for r in rows if r["reset_n"] and r["fetch_exception"])
    assert all(p["latency"] == 3 for p in loads)
    csv_write(evidence / "accepted_stores.csv", writes)
    csv_write(evidence / "platform_edges.csv", rows)
    csv_write(evidence / "fetch_responses.csv", fetches)
    csv_write(evidence / "load_responses.csv", loads)
    for p in source_files: assert digest(p.read_bytes()) == source_hashes[str(p)], f"Source changed during run: {p}"
    for p in out.iterdir():
        if p.is_file() and p.name != "all.vcd": shutil.copyfile(p, evidence / p.name)
    for name in ("qualification_events.csv", "sim-trace.log"):
        shutil.copyfile(out / "logs" / name, evidence / name)
    shutil.copyfile(build / "manifest.json", evidence / "simulator_manifest.json")
    summary = {"status": "passed" if exit_ok and stores_ok and issue["witness_found"] else "failed",
        "scope": "Finite qualification of declared external Harvard ROM/data platform; no optimization or universal occupancy proof",
        "core_rtl_source_edits": False, "upstream_commit": PRE_FPU_PIN,
        "platform": "ELF executable-only immutable instruction ROM; separate data memory object; original gap2 fetch pipeline and 3-cycle data service",
        "platform_not_claimed_equivalent_to_original_unified_memory": True,
        "program_exit_ok": exit_ok, "all_64_output_stores_and_exit_checked": stores_ok, "accepted_store_count": len(writes),
        "simulator_manifest_sha256": digest((build / "manifest.json").read_bytes()),
        "binary_sha256": manifest["binary_sha256"], "capacity_parameters": manifest["capacity_parameters"],
        "elf_images": image_record, "memory_timing": service, "out_of_order": issue, "occupancy": occupancy,
        "all_active_instruction_payloads_in_elf_words_or_zero": True,
        "all_observed_instruction_fault_payloads_zero": True,
        "source_sha256": source_hashes, "compile_commands": commands, "run_command": run,
        "raw_fst_sha256": digest((out / "logs/waves.fst").read_bytes())}
    (evidence / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    (evidence / "SHA256SUMS").write_text("".join(f"{digest(p.read_bytes())}  {p.name}\n" for p in sorted(evidence.iterdir()) if p.is_file() and p.name != "SHA256SUMS"))
    print(json.dumps({"status": summary["status"], "exit_ok": exit_ok, "stores_ok": stores_ok,
                      "ooo_witnesses": issue["actual_alu_issue_inversion_count"], "instruction_bytes": len(instruction)}))
    return 0 if summary["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
