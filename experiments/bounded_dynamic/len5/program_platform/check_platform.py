#!/usr/bin/env python3
"""Audit unchanged RTL/pipelines and test the actual Harvard lookup independently."""
from __future__ import annotations
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from prepare_frontend import PRE_FPU_PIN, digest, workspace_root
from platform_patch import patch_memory, START, END

TEST = r'''
module HarvardLookupTest;
  import len5_pkg::*;
  logic clk=0;
  always #5 clk=~clk;
  byte unsigned reference [0:55];
  logic [37:0] answer;
  logic [31:0] expected;
  logic [63:0] address;
  int checks=0;
  int ret;
  memory_bare_emu #(.PIPE_NUM(2), .SKIP_INS_ANS_REG(1), .SKIP_DATA_ANS_REG(0)) dut (
    .clk_i(clk), .rst_ni(1'b0), .instr_flush_i(1'b0),
    .mem_file_i(DATA_IMAGE), .mem_dump_file_i("unused"),
    .instr_valid_i(1'b0), .instr_ready_i(1'b1), .instr_addr_i(64'b0),
    .data_load_valid_i(1'b0), .data_load_ready_i(1'b1), .data_load_addr_i(64'b0),
    .data_load_be_i(8'hff), .data_load_tag_i('0),
    .data_store_valid_i(1'b0), .data_store_ready_i(1'b1), .data_store_we_i(1'b0),
    .data_store_addr_i(64'b0), .data_store_tag_i('0), .data_store_be_i(8'hff), .data_store_wdata_i(64'b0)
  );
  initial begin
    $readmemh(ROM_IMAGE, reference);
    #1;
    for (int i=0; i<68; i++) begin
      if (i<64) address=64'(i);
      else case(i)
        64: address=64'h1000;
        65: address=64'h1001;
        66: address=64'hfffffffffffffffc;
        67: address=64'hffffffffffffffff;
      endcase
      answer=dut.lookup_instruction_rom(address);
      if (address[1:0] != 0) begin
        assert(answer[37:6]==0 && answer[5] && answer[4:0]==E_I_ADDR_MISALIGNED)
          else $fatal(1,"Misaligned ROM response incorrect at %h",address);
      end else if (address >= 56) begin
        assert(answer[37:6]==0 && answer[5] && answer[4:0]==E_I_ACCESS_FAULT)
          else $fatal(1,"Unmapped ROM response incorrect at %h",address);
      end else begin
        expected={reference[address+3],reference[address+2],reference[address+1],reference[address]};
        assert(answer[37:6]==expected && !answer[5] && answer[4:0]==E_UNKNOWN)
          else $fatal(1,"Mapped ROM response incorrect at %h",address);
      end
      checks++;
    end
    ret=dut.mem.WriteW(0,32'hdeadbeef);
    assert(ret==0) else $fatal(1,"Data write failed");
    ret=dut.mem.ReadW(0);
    assert(ret==0 && dut.mem.read_word==32'hdeadbeef) else $fatal(1,"Data write not stored");
    answer=dut.lookup_instruction_rom(0);
    expected={reference[3],reference[2],reference[1],reference[0]};
    assert(answer[37:6]==expected && !answer[5]) else $fatal(1,"Data write changed instruction ROM");
    checks++;
    ret=dut.mem.WriteW(64'h1000,32'hfeedcafe);
    answer=dut.lookup_instruction_rom(64'h1000);
    assert(ret==0 && answer[37:6]==0 && answer[5] && answer[4:0]==E_I_ACCESS_FAULT)
      else $fatal(1,"Data address became executable");
    checks++;
    $display("HARVARD_LOOKUP_PASS checks=%0d", checks);
    $finish;
  end
endmodule
'''


def main():
    external = workspace_root(HERE) / "experiments/bounded_dynamic"
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--build", type=Path, default=external / "len5/build/harvard_gap2_platform_v1")
    ap.add_argument("--program", type=Path, default=external / "len5/build/harvard_streaming_v1")
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--evidence", type=Path, required=True)
    args = ap.parse_args()
    build, program, out, evidence = (x.resolve() for x in (args.build, args.program, args.output, args.evidence))
    manifest = json.loads((build / "manifest.json").read_text())
    assert manifest["instruction_memory_platform"] == "separate_immutable_elf_executable_rom"
    assert manifest["upstream_commit"] == PRE_FPU_PIN
    out.mkdir(parents=True, exist_ok=False); evidence.mkdir(parents=True, exist_ok=False)
    sources = []
    for name, expected in manifest["core_source_sha256"].items():
        path = build / name
        assert digest(path.read_bytes()) == expected
        upstream = subprocess.check_output(["git", "-C", str(external / "deps/len5"), "show", PRE_FPU_PIN + ":" + name.removeprefix("source/")])
        assert path.read_bytes() == upstream
        sources.append(str(path))
    memory = "tb/memory/memory_bare_emu.sv"
    original = subprocess.check_output(["git", "-C", str(external / "deps/len5"), "show", PRE_FPU_PIN + ":" + memory])
    prepared = (build / "source" / memory).read_bytes()
    assert patch_memory(original) == prepared
    assert digest(original) == manifest["testbench_original_sha256"][memory]
    assert digest(prepared) == manifest["testbench_prepared_sha256"][memory]
    for name, expected in manifest["harvard_source_sha256"].items(): assert digest((HERE / name).read_bytes()) == expected
    test = TEST.replace("DATA_IMAGE", json.dumps(str(program / "data.hex"))).replace("ROM_IMAGE", json.dumps(str(program / "instruction.hex")))
    (out / "HarvardLookupTest.sv").write_text(test)
    shutil.copyfile(__file__, out / "check_platform.py")
    command = ["/usr/bin/verilator", "--binary", "--timing", "--assert", "-Wno-fatal", "-j", "2",
        "--top-module", "HarvardLookupTest", "--Mdir", str(out / "obj_dir"),
        "-I" + str(build / "source/tb"), "-I" + str(build / "source/tb/memory"),
        *sources, str(build / "source" / memory), str(out / "HarvardLookupTest.sv")]
    env = {**os.environ, "PATH": "/usr/bin:/bin:/usr/local/bin"}
    with (out / "build.log").open("w") as f:
        subprocess.run(command, cwd=out, env=env, stdout=f, stderr=subprocess.STDOUT, check=True, timeout=120)
    run = [str(out / "obj_dir/VHarvardLookupTest"), "+instruction_rom=" + str(program / "instruction.hex")]
    with (out / "run.log").open("w") as f:
        subprocess.run(run, cwd=out, env=env, stdout=f, stderr=subprocess.STDOUT, check=True, timeout=30)
    assert "HARVARD_LOOKUP_PASS checks=70" in (out / "run.log").read_text()
    audit = {"status": "passed", "core_source_files_byte_equal_to_pinned_upstream": len(sources),
        "source_commit": PRE_FPU_PIN, "upstream_memory_sha256": digest(original), "prepared_memory_sha256": digest(prepared),
        "native_memory_logic_outside_instruction_lookup_byte_unchanged": True,
        "replaced_upstream_byte_interval": [original.index(START), original.index(END)],
        "source_control_preserved": "All native instruction/data pipeline, flush, readiness, and data-object access code outside the replaced lookup block",
        "lookup_cases": 68, "data_instruction_isolation_cases": 2,
        "lookup_cases_include_all_text_bytes_alignment_boundary_data_address_and_maximum_address": True,
        "instruction_fault_payload_zero_and_codes_checked": True,
        "independent_sv_readmemh_reference_checked": True,
        "compiled_original_patched_memory_module": True,
        "build_command": command, "run_command": run,
        "script_sha256": digest(Path(__file__).read_bytes()), "test_sha256": digest(test.encode()),
        "simulator_manifest_sha256": digest((build / "manifest.json").read_bytes()),
        "instruction_hex_sha256": digest((program / "instruction.hex").read_bytes()),
        "data_hex_sha256": digest((program / "data.hex").read_bytes()),
        "binary_sha256": digest((out / "obj_dir/VHarvardLookupTest").read_bytes())}
    (out / "summary.json").write_text(json.dumps(audit, indent=2) + "\n")
    for p in out.iterdir():
        if p.is_file(): shutil.copyfile(p, evidence / p.name)
    (evidence / "SHA256SUMS").write_text("".join(f"{digest(p.read_bytes())}  {p.name}\n" for p in sorted(evidence.iterdir()) if p.is_file() and p.name != "SHA256SUMS"))
    print(json.dumps(audit, indent=2))


if __name__ == "__main__":
    main()
