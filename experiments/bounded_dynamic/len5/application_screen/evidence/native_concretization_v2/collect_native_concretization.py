#!/usr/bin/env python3
"""Audit native counterexample artifacts and decode their observed trace; no runs."""
from __future__ import annotations
import argparse
import copy
import csv
import gzip
import json
from pathlib import Path
import shutil
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[3]))
from odc.temporal import digest


def vcd_values(path):
    names, values, snapshots = {}, {}, {}
    time = None
    for line in path.read_text().splitlines():
        if line.startswith("$var "):
            p = line.split(); names[p[3]] = p[4].lstrip("\\")
        elif line.startswith("#"):
            if time is not None: snapshots[time] = dict(values)
            time = int(line[1:])
        elif line.startswith("b"):
            value, ident = line[1:].split()
            values[names[ident]] = int(value, 2) if set(value) <= {"0", "1"} else None
        elif line and line[0] in "01xz" and not line.startswith("$jump"):
            values[names[line[1:]]] = int(line[0]) if line[0] in "01" else None
    if time is not None: snapshots[time] = dict(values)
    # Yosys's SAT VCD combines initial registers and time-step 1 at #0;
    # its subsequent labels are #2, #3, ... (WaveJSON uses index 1).
    assert 0 in snapshots and 1 not in snapshots and 2 in snapshots
    snapshots[1] = snapshots[0]
    return snapshots


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("abstract", type=Path)
    ap.add_argument("native", type=Path)
    ap.add_argument("evidence", type=Path)
    ap.add_argument("--observed", type=Path)
    ap.add_argument("--observed-evidence", type=Path)
    args = ap.parse_args()
    a, n, e = args.abstract, args.native, args.evidence
    summary = json.loads((n / "summary.json").read_text())
    original = json.loads((a / "source.json").read_text())
    native = json.loads((n / "native_core.json").read_text())
    expected = copy.deepcopy(original)
    module = expected["modules"]["datapath"]
    for alias, net in [("probe_insert", "insert"), ("probe_index", "new_idx")]:
        module["ports"][alias] = {"direction": "output", "bits": module["netnames"][
            "u_backend.u_exec_stage.u_alu_unit.u_arith_rs." + net]["bits"]}
    assert expected == native
    assert digest(a / "source.json") == summary["source_json_sha256"]
    assert digest(n / "native_core.json") == summary["native_core_sha256"]
    assert digest(n / "native_screen.json") == summary["native_screen_sha256"]
    assert digest(n / "AdmissionScreen.sv") == digest(a / "AdmissionScreen.sv") == summary["harness_sha256"]
    assert digest(n / "prepare.log") == summary["prepare"]["log_sha256"]
    assert digest(n / "native_query.log") == summary["query"]["log_sha256"]
    assert summary["status"] == "native_alphabet_prefix_counterexample"
    shown = vcd_values(n / "native_target.vcd")
    prefix = json.loads((n / "external_prefix.json").read_text())
    for row in prefix["frames"]:
        s = shown[row["sat_time"]]
        for field in ["rst_ni", "instruction_choice", "load_value"]: assert s[field] == row[field]
    assert shown[20]["probe_insert"] == 1 and shown[20]["probe_index"] == 3
    audit = {"native_source_matches_original_plus_only_two_probe_aliases": True,
             "native_harness_byte_identical_to_frozen_abstract_harness": True,
             "native_result": "counterexample at AIG frame19 / SAT time20; insert=1, slot=3",
             "native_query_seconds": summary["query"]["seconds"],
             "abstract_arithmetic_values_required": False,
             "exact_streaming_rom_counterexample_established": False,
             "accepted_optimization": False,
             "initial_state": summary["initial_state"],
             "summary_sha256": digest(n / "summary.json"),
             "native_trace_sha256": digest(n / "native_target.vcd"),
             "native_query_sha256": digest(n / "native_query.ys")}
    if args.observed:
        o, oe = args.observed, args.observed_evidence
        obs_summary = json.loads((o / "summary.json").read_text())
        assert obs_summary["status"] == "native_counterexample"
        assert digest(o / "query.log") == obs_summary["execution"]["log_sha256"]
        assert obs_summary["native_screen_sha256"] == summary["native_screen_sha256"]
        old_query = (n / "native_query.ys").read_text().split(" -dump_vcd ")[0]
        new_query = (o / "query.ys").read_text()
        assert new_query.startswith(old_query + " -show ")
        tail = new_query[len(old_query):].split(" -dump_vcd ")[0].split()
        assert tail[::2] == ["-show"] * len(obs_summary["added_observations"])
        assert tail[1::2] == obs_summary["added_observations"]
        obs = vcd_values(o / "native_observed.vcd")
        rs = "dut.u_backend.u_exec_stage.u_alu_unit.u_arith_rs."
        rows, accepted, conflicts, seen = [], [], [], {}
        for p in prefix["frames"]:
            t = p["sat_time"]; s = obs[t]
            for field in ["rst_ni", "instruction_choice", "load_value", "invalid_code_nonzero"]: assert s[field] == p[field]
            states = [(s[rs + "curr_state"] >> (3 * i)) & 7 for i in range(8)]
            next_states = [(s[rs + "next_state"] >> (3 * i)) & 7 for i in range(8)]
            row = {"aig_frame": t - 1, "sat_time": t, "rst_ni": s["rst_ni"],
                "instruction_choice": s["instruction_choice"], "selected_instruction_hex": f'{s["selected_instruction"]:08x}',
                "fetch_pc_hex": f'{s["instr_addr_o"]:016x}', "fetch_req": s["instr_req_o"],
                "fetch_grant": s["instr_gnt_i"], "fetch_accepted": s["instr_req_o"] & s["instr_gnt_i"],
                "flush": s["mem_flush_o"], "fetch_response_valid": s["instr_rvalid_i"],
                "fetch_response_word_hex": f'{s["instr_rdata_i"]:08x}',
                "alu_insert": s["probe_insert"], "alu_insert_slot": s["probe_index"],
                "alu_states_slot0_to7": ":".join(map(str, states)), "alu_live_count": sum(x != 0 for x in states),
                "alu_next_states_slot0_to7": ":".join(map(str, next_states)),
                "alu_next_live_count": sum(x != 0 for x in next_states),
                "alu_execute": s[rs + "ex_accepted"], "alu_save_result": s[rs + "save_res"],
                "alu_remove": s[rs + "remove"], "alu_result_hex": f'{s[rs+"eu_result_i"]:016x}',
                "alu_execute_slot": s[rs + "ex_idx"], "alu_remove_slot": s[rs + "cdb_idx"],
                "issue_dest_rob_idx": s[rs + "issue_dest_rob_idx_i"],
                "issue_rs1_rob_idx": (s[rs + "issue_rs1_i"] >> 64) & 31,
                "issue_rs1_ready": s[rs + "issue_rs1_i"] >> 69,
                "issue_rs2_ready": s[rs + "issue_rs2_i"] >> 69,
                "cdb_valid": s[rs + "cdb_valid_i"], "cdb_rob_idx": s[rs + "cdb_data_i"] >> 70,
                "load_req": s["data_load_req_o"], "load_response_valid": s["data_load_rvalid_i"],
                "load_addr_hex": f'{s["data_load_addr_o"]:016x}'}
            rows.append(row)
            if row["fetch_accepted"]:
                event = {k: row[k] for k in ["aig_frame", "fetch_pc_hex", "selected_instruction_hex", "flush", "rst_ni"]}
                accepted.append(event)
                pc, word = event["fetch_pc_hex"], event["selected_instruction_hex"]
                if pc in seen and seen[pc]["selected_instruction_hex"] != word:
                    conflicts.append({"earlier": seen[pc], "later": event})
                else: seen[pc] = event
        with (oe / "native_cycles.csv").open("w") as f:
            writer = csv.DictWriter(f, fieldnames=list(rows[0])); writer.writeheader(); writer.writerows(rows)
        assert rows[-1]["alu_insert"] == 1 and rows[-1]["alu_insert_slot"] == 3
        audit["observed_repeat"] = {"summary_sha256": digest(o / "summary.json"),
            "query_seconds": obs_summary["execution"]["seconds"], "only_added_observations_verified": True,
            "accepted_fetches": accepted, "immutable_rom_conflicts": conflicts,
            "this_trace_is_consistent_with_an_immutable_rom": not bool(conflicts),
            "interpretation": "Conflict excludes this trace, not every possible native witness for the prefix. With no conflicts, the observed finite fetches define a consistent partial immutable ROM.",
            "alu_admissions": [r for r in rows if r["alu_insert"]]}
        audit["observed_repeat"]["max_current_alu_occupancy"] = max(r["alu_live_count"] for r in rows)
        audit["observed_repeat"]["max_combinational_next_alu_occupancy"] = max(r["alu_next_live_count"] for r in rows)
        (oe / "trace_audit.json").write_text(json.dumps(audit["observed_repeat"], indent=2) + "\n")
    shutil.copyfile(__file__, e / "collect_native_concretization.py")
    (e / "prepare.log.gz").write_bytes(gzip.compress((n / "prepare.log").read_bytes(), mtime=0))
    (e / "AUDIT.json").write_text(json.dumps(audit, indent=2) + "\n")
    for target in [e] + ([args.observed_evidence] if args.observed_evidence else []):
        (target / "SHA256SUMS").write_text("".join(f"{digest(p)}  {p.name}\n" for p in sorted(target.iterdir()) if p.is_file() and p.name != "SHA256SUMS"))
    print(json.dumps(audit, indent=2))


if __name__ == "__main__":
    main()
