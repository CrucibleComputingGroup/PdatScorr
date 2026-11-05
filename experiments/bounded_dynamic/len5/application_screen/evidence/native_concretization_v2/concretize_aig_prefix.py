#!/usr/bin/env python3
"""Try a validated abstract witness's external prefix on original LEN5 RTL.

Only actual environment inputs are fixed. Abstract ALU/MUL values, witness
initial-state bits, and undefined RTL choices are NOT imposed on the original.
The first bounded target is AIG frame19 = Yosys SAT time20. No safety/optimization
acceptance follows from a successful bounded proof on this one input prefix.
"""
from __future__ import annotations
import argparse
import csv
import hashlib
import json
from pathlib import Path
import re
import shutil
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[3]))
sys.path.insert(0, str(HERE.parent))
from odc.temporal import checked_yosys, digest, formal_lower_command, run_command, validate_single_clock, yosys_path
from prepare_frontend import PRE_FPU_PIN, workspace_root

EXTERNAL = {"rst_ni": 1, "instruction_choice": 4, "load_value": 64, "invalid_code_nonzero": 3}


def read_aig(path):
    with path.open("rb") as f:
        header = f.readline().decode().split()
        assert header[0] == "aig" and len(header) == 10
        _, mi, ni, nl, no, na, nb, nc, nj, nf = header
        ni, nl, no, na, nb, nc, nj, nf = map(int, (ni, nl, no, na, nb, nc, nj, nf))
        assert nj == nf == no == 0
        for _ in range(nl + no + nb + nc): f.readline()
        for _ in range(2 * na):
            while True:
                b = f.read(1)
                if not b: raise ValueError("Truncated AIG AND section")
                if not b[0] & 128: break
        symbols = f.read().decode().splitlines()
    inputs = {}
    for line in symbols:
        match = re.fullmatch(r"i(\d+) (.+)", line)
        if match:
            index, name = int(match[1]), match[2]
            if name in inputs: raise ValueError("Duplicate input symbol")
            inputs[name] = index
    return header, inputs


def recover_prefix(source):
    summary = json.loads((source / "summary.json").read_text())
    bounded = source / "bounded_screen"
    bs = json.loads((bounded / "summary.json").read_text())
    validation = json.loads((bounded / "validation_execution.json").read_text())
    assert digest(source / "screen.aig") == summary["aig_sha256"] == bs["aig_sha256"]
    assert digest(bounded / "validate.log") == validation["log_sha256"]
    vlog = (bounded / "validate.log").read_text()
    assert "Counter-example verification succeeded." in vlog and "Main AIG: The cex is correct." in vlog
    header, symbols = read_aig(source / "screen.aig")
    rows = (bounded / "counterexample.aiw").read_text().splitlines()
    assert rows[-1] == "# DONE"
    # ABC fold adds one constraint-state latch and does not reorder PIs.
    assert len(rows[0]) == int(header[3]) + 1 and set(rows[0]) <= {"0", "1"}
    frames = rows[1:-1]
    assert len(frames) == 20
    assert all(len(row) == int(header[2]) and set(row) <= {"0", "1"} for row in frames)
    binding = {}
    for name, width in EXTERNAL.items():
        names = [name] if width == 1 else [f"{name}[{i}]" for i in range(width)]
        if any(n not in symbols for n in names): raise ValueError(f"Missing external AIG symbol: {name}")
        binding[name] = [symbols[n] for n in names]
    rows_out = []
    for frame, bits in enumerate(frames):
        row = {"aig_frame": frame, "sat_time": frame + 1}
        row.update({n: sum(int(bits[index]) << i for i, index in enumerate(indices))
                    for n, indices in binding.items()})
        row["selected_instruction"] = (summary["instruction_alphabet"][row["instruction_choice"]]
                                       if row["instruction_choice"] < 14 else "00000013")
        rows_out.append(row)
    assert rows_out[0]["rst_ni"] == 0
    # Independently crosscheck the PI order against ABC's named witness output.
    named = bounded / "counterexample.named.txt"
    indices = {b for bs in binding.values() for b in bs}
    count = 0
    for line in named.read_text().splitlines():
        match = re.fullmatch(r"pi(\d+)@(\d+)=([01])", line)
        if match and int(match[1]) in indices:
            index, frame, value = map(int, match.groups())
            assert int(frames[frame][index]) == value
            count += 1
    assert count == 20 * sum(EXTERNAL.values())
    return {"aig_header": header, "external_pi_indices_low_bit_first": binding,
            "named_pi_crosschecks": count, "frames": rows_out,
            "clock_convention": "AIG frame0 is SAT time1. Each step is a validated single-clock active edge; clk_i PI level is not used to schedule edges.",
            "unfixed": "Abstract result inputs, witness latch initial values and undefined RTL choices are not fixed. Native initial conditions and reset semantics remain legal."}


def main():
    workspace = workspace_root(HERE)
    builds = workspace / "experiments/bounded_dynamic/len5/build"
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=builds / "streaming_alphabet_gap2_v5_alu_mul")
    parser.add_argument("--output", type=Path, default=builds / "native_concretization_v1")
    parser.add_argument("--evidence", type=Path, default=HERE / "evidence/native_concretization_v1")
    parser.add_argument("--timeout", type=int, default=120)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    args.evidence.mkdir(parents=True, exist_ok=False)
    out, source = args.output.resolve(), args.source.resolve()
    shutil.copyfile(__file__, out / "concretize_aig_prefix.py")
    old = json.loads((source / "summary.json").read_text())
    assert old["source_commit"] == PRE_FPU_PIN and old["abstraction_mode"] == "alu_mul"
    assert digest(source / "source.json") == old["source_json_sha256"]
    assert digest(source / "AdmissionScreen.sv") == old["harness_sha256"]
    prefix = recover_prefix(source)
    (out / "external_prefix.json").write_text(json.dumps(prefix, indent=2) + "\n")
    with (out / "external_prefix.csv").open("w") as f:
        writer = csv.DictWriter(f, fieldnames=list(prefix["frames"][0]))
        writer.writeheader(); writer.writerows(prefix["frames"])
    native = json.loads((source / "source.json").read_text())
    mod = native["modules"]["datapath"]
    assert not any(c["type"] == "$anyseq" for c in mod["cells"].values())
    for alias, original in (("probe_insert", "insert"), ("probe_index", "new_idx")):
        mod["ports"][alias] = {"direction": "output", "bits": mod["netnames"][
            "u_backend.u_exec_stage.u_alu_unit.u_arith_rs." + original]["bits"]}
    (out / "native_core.json").write_text(json.dumps(native) + "\n")
    shutil.copyfile(source / "AdmissionScreen.sv", out / "AdmissionScreen.sv")
    yosys = str(workspace / "tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys")
    record = {"status": "preparing", "accepted_optimization": False,
        "scope": "Bounded native-core concretization of one abstract witness external prefix; not an unbounded safety proof or exact-ROM workload claim",
        "source_commit": PRE_FPU_PIN, "source_json_sha256": old["source_json_sha256"],
        "abstract_aig_sha256": old["aig_sha256"], "abstract_witness_sha256": digest(source / "bounded_screen/counterexample.aiw"),
        "native_core_sha256": digest(out / "native_core.json"), "harness_sha256": digest(out / "AdmissionScreen.sv"),
        "script_sha256": digest(Path(__file__)), "external_prefix_sha256": digest(out / "external_prefix.json"),
        "fixed_external_signals": EXTERNAL, "target_aig_frame": 19, "target_sat_time": 20,
        "initial_state": "Only original init attributes and the original initial reset premise. No set-init-zero and no abstract witness state imposed.",
        "native_changes": "Two read-only original RS probe ports; no original cell or connection changes, no ALU/MUL abstraction"}
    def save(): (out / "summary.json").write_text(json.dumps(record, indent=2) + "\n")
    save()
    try:
        record["prepare"] = checked_yosys(yosys,
            f"read_json {yosys_path(out/'native_core.json')}\nrename datapath ObservedCore\n"
            "bwmuxmap\nbmuxmap\ndemuxmap\n"
            f"read_verilog -formal -sv {yosys_path(out/'AdmissionScreen.sv')}\n"
            "prep -top AdmissionScreen -flatten\ncheck -assert\n" + formal_lower_command(yosys) +
            "select -assert-count 3 t:$assert\nselect *\nmemory_map\nopt_clean\nasync2sync\ndffunmap\n"
            "setundef -anyseq\nopt -keepdc\ndffunmap\nsetundef -anyseq\n"
            f"write_json {yosys_path(out/'native_screen.json')}\n", out, "prepare", args.timeout)
        model = json.loads((out / "native_screen.json").read_text())
        record["clock_model"] = validate_single_clock(model, "AdmissionScreen")
        record["native_screen_sha256"] = digest(out / "native_screen.json")
        sets = []
        for row in prefix["frames"]:
            for name, width in EXTERNAL.items():
                sets += ["-set-at", str(row["sat_time"]), name, f"{width}'h{row[name]:x}"]
        query = (f"read_json {yosys_path(out/'native_screen.json')}\ncheck -assert\n"
                 "sat -seq 20 -prove-asserts -prove-skip 19 -set-assumes " + " ".join(sets) +
                 f" -timeout {args.timeout} -show rst_ni -show instruction_choice -show load_value"
                 " -show probe_insert -show probe_index"
                 f" -dump_vcd {yosys_path(out/'native_target.vcd')} -dump_json {yosys_path(out/'native_target.json')}\n")
        (out / "native_query.ys").write_text(query)
        record["status"] = "query_running"; save()
        record["query"] = run_command([yosys, "-Q", "-T", "-s", str(out / "native_query.ys")], out / "native_query.log", args.timeout)
        log = (out / "native_query.log").read_text()
        if record["query"]["timeout"] or record["query"]["returncode"]:
            record["status"] = "unknown"
        elif "SAT proof finished - no model found: SUCCESS!" in log:
            record["status"] = "fixed_prefix_no_native_violation_at_frame19"
        elif "SAT proof finished - model found: FAIL!" in log:
            record["status"] = "native_alphabet_prefix_counterexample"
        else:
            record["status"] = "unknown"
    except (ValueError, RuntimeError, AssertionError, OSError) as error:
        record.update(status="error", error=str(error))
    assert digest(Path(__file__)) == record["script_sha256"], "Runner changed during run"
    save()
    for name in ("concretize_aig_prefix.py", "external_prefix.json", "external_prefix.csv", "AdmissionScreen.sv",
                 "summary.json", "prepare.ys", "native_query.ys", "native_query.log", "native_target.vcd", "native_target.json"):
        if (out / name).exists(): shutil.copyfile(out / name, args.evidence / name)
    (args.evidence / "SHA256SUMS").write_text("".join(f"{digest(p)}  {p.name}\n" for p in sorted(args.evidence.iterdir()) if p.is_file()))
    print(json.dumps(record, indent=2))


if __name__ == "__main__":
    main()
