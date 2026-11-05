#!/usr/bin/env python3
"""Repeat a source-bound native concretization, adding observations only."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import shutil
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[3]))
from odc.temporal import digest, run_command, yosys_path


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("source", type=Path)
    ap.add_argument("output", type=Path)
    ap.add_argument("evidence", type=Path)
    ap.add_argument("--timeout", type=int, default=120)
    args = ap.parse_args()
    source, out, evidence = args.source.resolve(), args.output.resolve(), args.evidence.resolve()
    old = json.loads((source / "summary.json").read_text())
    assert old["status"] == "native_alphabet_prefix_counterexample"
    assert digest(source / "native_screen.json") == old["native_screen_sha256"]
    assert digest(source / "native_query.log") == old["query"]["log_sha256"]
    model = json.loads((source / "native_screen.json").read_text())["modules"]["AdmissionScreen"]
    observations = ["invalid_code_nonzero", "instr_addr_o", "instr_req_o", "instr_gnt_i", "mem_flush_o",
        "selected_instruction", "instr_rdata_i", "instr_rvalid_i", "instr_rready_o",
        "data_load_req_o", "data_load_rvalid_i", "data_load_tag_o", "data_load_tag_i", "data_load_addr_o"]
    rs = "dut.u_backend.u_exec_stage.u_alu_unit.u_arith_rs."
    observations += [rs + n for n in ["curr_state", "next_state", "ex_idx", "cdb_idx", "remove", "ex_accepted",
        "save_res", "eu_valid_i", "eu_valid_o", "cdb_ready_i", "cdb_valid_o", "cdb_valid_i", "cdb_data_i",
        "flush_i", "issue_rs1_i", "issue_rs2_i", "issue_dest_rob_idx_i", "issue_eu_ctl_i", "eu_result_i"]]
    assert all(n in model["netnames"] for n in observations)
    out.mkdir(parents=True, exist_ok=False)
    evidence.mkdir(parents=True, exist_ok=False)
    original = (source / "native_query.ys").read_text()
    prefix = original.split(" -dump_vcd ")[0]
    assert len(original.split(" -dump_vcd ")) == 2
    query = prefix + "".join(" -show " + n for n in observations)
    query += f" -dump_vcd {yosys_path(out/'native_observed.vcd')} -dump_json {yosys_path(out/'native_observed.json')}\n"
    (out / "query.ys").write_text(query)
    shutil.copyfile(__file__, out / "concretize_observe.py")
    rec = {"status": "running", "accepted_optimization": False,
        "source_summary_sha256": digest(source / "summary.json"),
        "source_query_sha256": digest(source / "native_query.ys"),
        "native_screen_sha256": old["native_screen_sha256"],
        "query_sha256": digest(out / "query.ys"), "script_sha256": digest(Path(__file__)),
        "changes": "Only additional -show observations and dump destinations; source, constraints, target and timeout unchanged",
        "added_observations": observations}
    (out / "summary.json").write_text(json.dumps(rec, indent=2) + "\n")
    rec["execution"] = run_command([old["query"]["argv"][0], "-Q", "-T", "-s", str(out / "query.ys")], out / "query.log", args.timeout)
    log = (out / "query.log").read_text()
    rec["status"] = ("native_counterexample" if not rec["execution"]["timeout"] and rec["execution"]["returncode"] == 0
                     and "SAT proof finished - model found: FAIL!" in log else "unknown_or_error")
    assert digest(Path(__file__)) == rec["script_sha256"]
    (out / "summary.json").write_text(json.dumps(rec, indent=2) + "\n")
    for p in out.iterdir():
        if p.is_file(): shutil.copyfile(p, evidence / p.name)
    (evidence / "SHA256SUMS").write_text("".join(f"{digest(p)}  {p.name}\n" for p in sorted(evidence.iterdir()) if p.is_file()))
    print(json.dumps(rec, indent=2))


if __name__ == "__main__":
    main()
