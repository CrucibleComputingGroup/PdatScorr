#!/usr/bin/env python3
"""Simulation witnesses of varying flip-flop bits under randomized platform timing.

The platform is the closed formal platform of one export_closed.py model with its
two timing mechanisms replaced, for simulation only. The fetch acceptance gate is
a testbench input instead of the fixed gap counter. The data service grants each
request at random and replies in order after a random delay of at least one cycle,
instead of granting every request and replying after exactly three cycles. The ROM,
zero fault payload, load values, reset stimuli and observation are those of
witness.py. LEN5 holds each memory request until it is granted, matches replies by
tag and is always ready for replies, so every such schedule is a legal timing of
the same program. The testbench changes the timing regime every 256 to 4096
cycles: a periodic or random fetch gate, and random grant and reply rates.

A bit witnessed varying here changes in some execution of the program under some
legal timing, so it is not constant under the ISA/program constraints alone: no
analysis given only that information can remove it. The run classifies the
constants certified for each fixed-timing platform. Bits never witnessed here are
not thereby proved constant; this is finite simulation evidence.
"""
from __future__ import annotations

import argparse
import concurrent.futures
import csv
import json
import os
from pathlib import Path
import random
import re
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
sys.path.insert(0, str(REPO))
sys.path.insert(0, str(HERE))
from odc.temporal import digest, export_design  # noqa: E402
from export_closed import flip_flop_manifest, observed_design  # noqa: E402
from cosim import (PROBES, data_image, fill, hex_vector, parse_result,  # noqa: E402
                   replace_once, seed_no_reset_flip_flops, sim_platform)
from witness import classify, witness_testbench  # noqa: E402
from prepare_frontend import workspace_root  # noqa: E402

TIMING_INPUTS = ("fetch_gate", "load_gnt", "load_reply", "store_gnt", "store_reply")
FIXED_GATE = "  wire gate_open = gap_left == 0;\n"
FIXED_SERVICE = """\
  // A fully pipelined data service; flush never cancels data replies.
  reg [2:0] lv, sv;
  reg [3:0] lt0, lt1, lt2, st0, st1, st2;
  reg [63:0] ld0, ld1, ld2;
  assign data_load_gnt_i = rst_ni; assign data_store_gnt_i = rst_ni;
  assign data_load_rvalid_i = lv[2]; assign data_store_rvalid_i = sv[2];
  assign data_load_tag_i = lt2; assign data_store_tag_i = st2;
  assign data_load_rdata_i = ld2;
  always @(posedge clk_i) begin
    if (!rst_ni) begin
      lv <= 0; sv <= 0; lt0 <= 0; lt1 <= 0; lt2 <= 0;
      st0 <= 0; st1 <= 0; st2 <= 0; ld0 <= 0; ld1 <= 0; ld2 <= 0;
    end else begin
      lv <= {lv[1:0], data_load_req_o}; sv <= {sv[1:0], data_store_req_o};
      lt0 <= data_load_tag_o; lt1 <= lt0; lt2 <= lt1;
      st0 <= data_store_tag_o; st1 <= st0; st2 <= st1;
      ld0 <= load_value; ld1 <= ld0; ld2 <= ld1;
    end
  end
"""
RANDOM_SERVICE = """\
  // Randomized data service (simulation only): random grants; replies in order
  // after a random delay of at least one cycle; flush never cancels data replies.
  reg [3:0] lq_tag [0:15]; reg [63:0] lq_data [0:15]; reg [3:0] sq_tag [0:15];
  reg [4:0] lq_count, sq_count;
  reg [3:0] lq_head, lq_tail, sq_head, sq_tail;
  reg l_offer, s_offer;
  wire l_push = data_load_req_o && data_load_gnt_i, l_pop = data_load_rvalid_i && data_load_rready_o;
  wire s_push = data_store_req_o && data_store_gnt_i, s_pop = data_store_rvalid_i && data_store_rready_o;
  wire [4:0] lq_next = lq_count + {4'd0, l_push} - {4'd0, l_pop};
  wire [4:0] sq_next = sq_count + {4'd0, s_push} - {4'd0, s_pop};
  assign data_load_gnt_i = rst_ni && load_gnt && lq_count != 5'd16;
  assign data_store_gnt_i = rst_ni && store_gnt && sq_count != 5'd16;
  assign data_load_rvalid_i = l_offer; assign data_store_rvalid_i = s_offer;
  assign data_load_tag_i = lq_tag[lq_head]; assign data_store_tag_i = sq_tag[sq_head];
  assign data_load_rdata_i = lq_data[lq_head];
  always @(posedge clk_i) begin
    if (!rst_ni) begin
      lq_count <= 0; sq_count <= 0; lq_head <= 0; lq_tail <= 0; sq_head <= 0; sq_tail <= 0;
      l_offer <= 0; s_offer <= 0;
    end else begin
      if (l_push) begin lq_tag[lq_tail] <= data_load_tag_o; lq_data[lq_tail] <= load_value; lq_tail <= lq_tail + 4'd1; end
      if (s_push) begin sq_tag[sq_tail] <= data_store_tag_o; sq_tail <= sq_tail + 4'd1; end
      if (l_pop) lq_head <= lq_head + 4'd1;
      if (s_pop) sq_head <= sq_head + 4'd1;
      lq_count <= lq_next; sq_count <= sq_next;
      l_offer <= (l_offer && !l_pop) || (load_reply && lq_next != 5'd0);
      s_offer <= (s_offer && !s_pop) || (store_reply && sq_next != 5'd0);
    end
  end
"""
FAULT_DATA_PORT = "input wire [31:0] instruction_fault_data,\n"


def randomized_platform(formal: str) -> str:
    """The formal platform text with randomized fetch gating and data service."""
    text = replace_once(formal, FIXED_GATE, "  wire gate_open = fetch_gate;  // randomized (simulation only)\n")
    text = replace_once(text, FIXED_SERVICE, RANDOM_SERVICE)
    return replace_once(text, FAULT_DATA_PORT, FAULT_DATA_PORT + f"  input wire {', '.join(TIMING_INPUTS)},\n")


TIMING_DECLS = """\
  logic fetch_gate = 1'b1, load_gnt = 1'b1, load_reply = 1'b1, store_gnt = 1'b1, store_reply = 1'b1;
  int unsigned regime_left = 0, fetch_period, p_fetch, p_lgnt, p_lrep, p_sgnt, p_srep;
  longint unsigned regimes, gate_closed, load_waits, store_waits;
  int unsigned max_lq, max_sq;
"""
TIMING_DRAWS = """\
      // Timing regime: periodic or random fetch gate, random grant and reply rates.
      if (regime_left == 0) begin
        regimes++;
        case ($urandom % 3) 0: regime_left = 256; 1: regime_left = 1024; default: regime_left = 4096; endcase
        fetch_period = ($urandom % 2 == 0) ? 1 + $urandom % 4 : 0;
        case ($urandom % 5) 0: p_fetch = 10; 1: p_fetch = 25; 2: p_fetch = 50; 3: p_fetch = 75; default: p_fetch = 90; endcase
        case ($urandom % 4) 0: p_lgnt = 25; 1: p_lgnt = 50; 2: p_lgnt = 75; default: p_lgnt = 100; endcase
        case ($urandom % 4) 0: p_sgnt = 25; 1: p_sgnt = 50; 2: p_sgnt = 75; default: p_sgnt = 100; endcase
        case ($urandom % 4) 0: p_lrep = 5; 1: p_lrep = 20; 2: p_lrep = 50; default: p_lrep = 100; endcase
        case ($urandom % 4) 0: p_srep = 5; 1: p_srep = 20; 2: p_srep = 50; default: p_srep = 100; endcase
      end
      regime_left--;
      fetch_gate = fetch_period != 0 ? (cyc % fetch_period == 0) : ($urandom % 100 < p_fetch);
      load_gnt = $urandom % 100 < p_lgnt;
      load_reply = $urandom % 100 < p_lrep;
      store_gnt = $urandom % 100 < p_sgnt;
      store_reply = $urandom % 100 < p_srep;
"""
TIMING_COUNTS = """\
      if (!fetch_gate) gate_closed++;
      if (o_load && !orig.data_load_gnt_i) load_waits++;
      if (o_store && !orig.data_store_gnt_i) store_waits++;
      if (32'(orig.lq_count) > max_lq) max_lq = 32'(orig.lq_count);
      if (32'(orig.sq_count) > max_sq) max_sq = 32'(orig.sq_count);
"""
TIMING_REPORT = """\
    $display("COSIM timing_regimes %0d", regimes);
    $display("COSIM fetch_gate_closed %0d", gate_closed);
    $display("COSIM load_grant_waits %0d", load_waits);
    $display("COSIM store_grant_waits %0d", store_waits);
    $display("COSIM max_outstanding_loads %0d", max_lq);
    $display("COSIM max_outstanding_stores %0d", max_sq);
"""


def timing_testbench() -> str:
    """The witness.py testbench driving the randomized timing inputs; it counts accepted requests only."""
    tb = replace_once(witness_testbench(), "// Generated by witness.py from the cosim.py testbench.",
                      "// Generated by timing_witness.py from the witness.py testbench.")
    tb = replace_once(tb, "  Platform_orig orig(.clk_i(clk), .rst_ni(rst_ni), .instruction_choice(instruction_choice),\n",
                      "  Platform_orig orig(.clk_i(clk), .rst_ni(rst_ni), .instruction_choice(instruction_choice),\n"
                      + "    " + ", ".join(f".{n}({n})" for n in TIMING_INPUTS) + ",\n")
    tb = replace_once(tb, "  logic [31:0] instruction_fault_data = '0;\n",
                      "  logic [31:0] instruction_fault_data = '0;\n" + TIMING_DECLS)
    tb = replace_once(tb, "      instruction_fault_data = $urandom;\n",
                      "      instruction_fault_data = $urandom;\n" + TIMING_DRAWS)
    tb = replace_once(tb, "      if (o_load) loads++;\n", "      if (o_load && orig.data_load_gnt_i) loads++;\n")
    tb = replace_once(tb, "      if (o_store) begin\n", "      if (o_store && orig.data_store_gnt_i) begin\n")
    tb = replace_once(tb, "      if (o_flush) flushes++;\n", "      if (o_flush) flushes++;\n" + TIMING_COUNTS)
    tb = replace_once(tb, "    {reset_frames, rereset_events, reset_admissions} = '0;\n",
                      "    {reset_frames, rereset_events, reset_admissions} = '0;\n"
                      "    {regimes, gate_closed, load_waits, store_waits} = '0;\n    {max_lq, max_sq} = '0;\n")
    return replace_once(tb, '    $display("COSIM digest %016x", trace_digest);\n',
                        TIMING_REPORT + '    $display("COSIM digest %016x", trace_digest);\n')


def bit_names(bits: set[int], records: list[dict]) -> list[dict]:
    return [{"cell": records[i]["cell"], "bit": records[i]["bit"], "net": records[i]["net"],
             "value": records[i]["reset"]} for i in sorted(bits)]


def main() -> int:
    workspace = workspace_root(HERE)
    bin_dir = workspace / "tools/oss-cad-suite-20261104/oss-cad-suite/bin"
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--model", type=Path, required=True, help="export_closed.py output whose platform is randomized")
    ap.add_argument("--reach", action="append", required=True, metavar="NAME=REACH_DIR",
                    help="Certified reach.py output on the same design (any fixed-timing platform)")
    ap.add_argument("--evidence", type=Path, required=True, help="Recorded RTL platform simulation evidence")
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--seeds", type=int, default=512)
    ap.add_argument("--cycles", type=int, default=1000000)
    ap.add_argument("--reset-periods", type=int, nargs="+", default=[300, 1000, 3000, 0],
                    help="Mean cycles between random re-resets, cycled over seeds (0: none)")
    ap.add_argument("--image-seeds", type=int, default=16)
    ap.add_argument("--image-cycle-factor", type=int, default=40,
                    help="Image runs simulate this multiple of the recorded program length")
    ap.add_argument("--x-assign", choices=("0", "1"), default="0")
    ap.add_argument("--yosys", default=str(bin_dir / "yosys"))
    ap.add_argument("--verilator", default=str(bin_dir / "verilator"))
    ap.add_argument("--jobs", type=int, default=min(64, os.cpu_count() or 1))
    ap.add_argument("--timeout", type=int, default=7200)
    args = ap.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    shutil.copyfile(Path(__file__), out / "timing_witness.py")
    model = args.model.resolve()
    summary = json.loads((model / "summary.json").read_text())
    if summary.get("status") != "exported" or digest(model / "ClosedPlatform.sv") != summary["platform_sha256"]:
        raise ValueError("Model directory does not match its export record")
    if digest(args.evidence / "instruction.hex") != digest(model / "program.hex"):
        raise ValueError("Evidence program differs from the model ROM image")
    design_path = Path(summary["design"])
    if digest(design_path) != summary["design_sha256"]:
        raise ValueError("Original design changed since export")
    original = json.loads(design_path.read_text())
    records = flip_flop_manifest(original)
    manifest = json.loads((model / "manifest.json").read_text())
    if [(r["cell"], r["bit"], r["net"]) for r in records] != \
            [(r["cell"], r["bit"], r["net"]) for r in manifest["records"]]:
        raise ValueError("Flip-flop manifest differs from the model")
    index = {(r["cell"], r["bit"]): i for i, r in enumerate(records)}

    sets, sources = {}, []
    for spec in args.reach:
        name, _, path = spec.partition("=")
        if not re.fullmatch(r"[a-z][a-z0-9]*", name) or name in sets or not path:
            ap.error(f"Bad --reach {spec}")
        rdir = Path(path).resolve()
        reach = json.loads((rdir / "summary.json").read_text())
        constants = json.loads((rdir / "constants.json").read_text())
        if reach.get("status") != "certified" or constants.get("status") != "certified" \
                or digest(rdir / "constants.json") != reach["constants_sha256"] \
                or reach["design_sha256"] != summary["design_sha256"]:
            raise ValueError(f"{rdir} is not a certified reachability run on this design")
        bits = set()
        for c in constants["constants"]:
            i = index[(c["cell"], c["bit"])]
            if records[i]["reset"] is None or c["value"] != records[i]["reset"]:
                raise ValueError(f"{rdir}: constant {c['cell']}[{c['bit']}] differs from its reset value")
            bits.add(i)
        sets[name] = bits
        sources.append({"name": name, "reach": str(rdir), "reach_summary_sha256": digest(rdir / "summary.json"),
                        "constants_sha256": reach["constants_sha256"], "model_aig_sha256": reach["model_aig_sha256"],
                        "gap": reach["instruction_acceptance_gap"], "constant_bits": len(bits)})
    common = set.intersection(*sets.values())

    observed = observed_design(original, records)
    ports = observed["modules"]["datapath"]["ports"]
    outputs = sorted((n, len(p["bits"])) for n, p in ports.items()
                     if p["direction"] == "output" and n not in PROBES)
    verilog = out / "core_orig.v"
    export_design(observed, "datapath", "Core_orig", verilog, args.yosys, args.timeout)
    if digest(verilog.with_suffix(".json")) != summary["core_json_sha256"]:
        raise ValueError("Original observed core differs from the formal model's core")
    text, no_reset = seed_no_reset_flip_flops(verilog.read_text(), records)
    (out / "sim_core_orig.v").write_text(text)
    formal = (model / "ClosedPlatform.sv").read_text()
    ptext, info = sim_platform(randomized_platform(formal), "orig", "Core_orig", outputs)
    (out / "platform_orig.sv").write_text(ptext)
    base, words = data_image(args.evidence / "data.hex")
    (out / "image.hex").write_text("".join(f"{w:016x}\n" for w in words))
    zero = hex_vector([0] * len(records))
    wmask = [int(r["reset"] is not None) for r in records]
    wval = [r["reset"] or 0 for r in records]
    tb = fill(timing_testbench(), W=len(records), K=sum(w for _, w in outputs), NV=1, THRESHOLD=0,
              CMASK=zero, CVAL=zero, WMASK=hex_vector(wmask), WVAL=hex_vector(wval),
              IMG_BASE=f"{base:x}", IMG_WORDS=len(words), INSTANCES="", CHECKS="")
    (out / "tb.sv").write_text(tb)
    files = [out / "sim_core_orig.v", out / "platform_orig.sv", out / "tb.sv"]

    env = dict(os.environ, PATH=f"{bin_dir}:/usr/bin:/bin")
    version = subprocess.run([args.verilator, "--version"], env=env, capture_output=True, text=True, check=True).stdout.strip()
    argv = [args.verilator, "--binary", "-j", str(args.jobs), "--x-assign", args.x_assign, "--x-initial", "unique",
            "-Wno-fatal", "-Wno-lint", "-Wno-style", "-Wno-MULTIDRIVEN", "--top-module", "tb",
            "-Mdir", str(out / "obj"), "-o", "simv"] + [str(f) for f in files]
    start = time.time()
    with (out / "build.log").open("w") as log:
        build = subprocess.run(argv, env=env, stdout=log, stderr=subprocess.STDOUT, timeout=args.timeout)
    record = {
        "status": "running", "scope": __doc__.strip().splitlines()[0],
        "model": str(model), "model_aig_sha256": summary["aig_sha256"],
        "replaced_timing": {"fetch_gate": "testbench input (periodic 1-4 or random 10-90% per regime)",
                            "data_service": "random grants 25-100%, in-order replies, reply rate 5-100% per cycle, "
                                            "at most 16 outstanding per channel"},
        "design_sha256": summary["design_sha256"], "reach_sources": sources,
        "evidence": str(args.evidence.resolve()), "data_image_sha256": digest(args.evidence / "data.hex"),
        "flip_flop_bits": len(records), "reset_flip_flop_bits": sum(wmask),
        "no_reset_flip_flops": [{"ffq_lsb": lo, "width": w} for lo, w in no_reset],
        "service_assertions": info["service_assertions"],
        "verilator": version, "x_assign": args.x_assign,
        "build": {"argv": argv, "returncode": build.returncode, "seconds": round(time.time() - start, 1),
                  "log_sha256": digest(out / "build.log")},
        "sources_sha256": {f.name: digest(f) for f in files + [out / "image.hex"]},
        "script_sha256": digest(Path(__file__)),
    }
    (out / "summary.json").write_text(json.dumps(record, indent=2) + "\n")
    if build.returncode != 0:
        raise RuntimeError("Verilator build failed; see build.log")

    expected_stores = [(int(r["data_store_addr_o"]), int(r["data_store_wdata_o"]), int(r["data_store_be_o"]))
                       for r in csv.DictReader((args.evidence / "accepted_stores.csv").open())]
    last_store = max(int(r["time"]) for r in csv.DictReader((args.evidence / "accepted_stores.csv").open())) // 2
    runs = [{"seed": s + 1, "image": False, "cycles": args.cycles,
             "reset_period": args.reset_periods[s % len(args.reset_periods)]} for s in range(args.seeds)]
    runs += [{"seed": 1001 + s, "image": True, "cycles": args.image_cycle_factor * last_store + 1000, "reset_period": 0}
             for s in range(args.image_seeds)]

    def execute(run: dict) -> dict:
        rng = random.Random(run["seed"])
        plus = [f"+finit_{lo}={rng.getrandbits(w):x}" for lo, w in no_reset]
        plus += [f"+pinit_{n}={rng.getrandbits(w):x}" for n, w in info["registers"]]
        tag = f"{'image' if run['image'] else 'random'}_{run['seed']}"
        argv = [str(out / "obj/simv"), f"+verilator+seed+{run['seed']}", "+verilator+rand+reset+2",
                f"+cycles={run['cycles']}", f"+reset_period={run['reset_period']}", f"+image={int(run['image'])}"]
        if run["image"]:
            argv += [f"+image_file={out / 'image.hex'}", f"+store_log={out / (tag + '.stores.csv')}"]
        t0 = time.time()
        proc = subprocess.run(argv + plus, env=env, capture_output=True, text=True, timeout=args.timeout)
        (out / f"{tag}.log").write_text(proc.stdout + proc.stderr)
        result = parse_result(proc.stdout)
        lines = [line.split()[1] for line in proc.stdout.splitlines() if line.startswith("WITNESS ")]
        seen = int(lines[0], 16) if len(lines) == 1 and re.fullmatch(r"[0-9a-f]+", lines[0]) else None
        result.update(run, returncode=proc.returncode, seconds=round(time.time() - t0, 1),
                      log_sha256=digest(out / f"{tag}.log"),
                      witnessed_bits=None if seen is None else bin(seen).count("1"))
        result["seen"] = seen
        if run["image"]:
            got = [tuple(int(x) for x in line.split(","))[1:] for line in
                   (out / f"{tag}.stores.csv").read_text().splitlines()]
            result["image_stores"] = {"recorded": len(expected_stores), "simulated": len(got),
                                      "values_match": got == expected_stores,
                                      "store_log_sha256": digest(out / f"{tag}.stores.csv")}
        return result

    with concurrent.futures.ThreadPoolExecutor(max_workers=min(len(runs), args.jobs)) as pool:
        results = list(pool.map(execute, runs))
    failures, union = [], 0
    for r in results:
        where = f"seed {r['seed']}"
        if r["returncode"] != 0 or "digest" not in r or r["seen"] is None or r.get("simulated_cycles") != r["cycles"] \
                or r.get("image_mode") != int(r["image"]) or r.get("reset_period_arg") != r["reset_period"]:
            failures.append(f"{where}: simulation did not finish")
            continue
        union |= r["seen"]
        if r["service_fail"]["cycles"]:
            failures.append(f"{where}: a data reply was offered while the core was not ready, cycle "
                            f"{r['service_fail']['first']}")
        if r["fetches"] == 0 or r["stores"] == 0:
            failures.append(f"{where}: no activity")
        if r["image"] and not r["image_stores"]["values_match"]:
            failures.append(f"{where}: stores differ from the recorded RTL simulation")
        elif not r["image"] and r["reset_period"] and not r["rereset_events"]:
            failures.append(f"{where}: no re-reset occurred")
    for r in results:
        del r["seen"], r["bits"], r["mism"]
    witnessed = {i for i in range(len(records)) if union >> i & 1}
    reset_bits = {i for i, r in enumerate(records) if r["reset"] is not None}
    if witnessed - reset_bits:
        failures.append("A flip-flop without reset was recorded")
    increments = {s["name"]: classify(sets[s["name"]] - common, witnessed, records) for s in sources}
    record.update(
        status="passed" if not failures else "failed", failures=failures, runs=results,
        totals={"runs": len(results), "cycles": sum(r["cycles"] for r in results),
                "rereset_events": sum(r["rereset_events"] for r in results),
                "timing_regimes": sum(r["timing_regimes"] for r in results),
                "fetch_gate_closed_cycles": sum(r["fetch_gate_closed"] for r in results),
                "load_grant_waits": sum(r["load_grant_waits"] for r in results),
                "store_grant_waits": sum(r["store_grant_waits"] for r in results),
                "max_outstanding_loads": max(r["max_outstanding_loads"] for r in results),
                "max_outstanding_stores": max(r["max_outstanding_stores"] for r in results),
                "fetches": sum(r["fetches"] for r in results), "loads": sum(r["loads"] for r in results),
                "stores": sum(r["stores"] for r in results),
                "alu_rs_admissions_by_row": {k: sum(r["adm"][k] for r in results) for k in range(8)},
                "service_assertion_violation_cycles": sum(r["service_fail"]["cycles"] for r in results),
                "distinct_trace_digests": len({r["digest"] for r in results})},
        witnessed_varying_bits=len(witnessed),
        certified={s["name"]: classify(sets[s["name"]], witnessed, records) for s in sources},
        common_to_all_sources=classify(common, witnessed, records),
        beyond_common=increments,
        never_certified=classify(reset_bits - set.union(*sets.values()), witnessed, records),
    )
    (out / "summary.json").write_text(json.dumps(record, indent=2) + "\n")
    bound = common - witnessed
    (out / "program_only_bound.json").write_text(json.dumps({
        "status": "simulation_bound_not_certified",
        "meaning": ("Constants common to every listed fixed-timing platform that were never witnessed varying under "
                    "randomized timing: an upper bound, from finite simulation, on the flip-flop constants that the "
                    "ISA/program constraints alone imply. Not a proof; not usable for substitution."),
        "design_sha256": summary["design_sha256"], "witness_summary_sha256": digest(out / "summary.json"),
        "constant_bits": len(bound), "constants": bit_names(bound, records)}) + "\n")
    brief = lambda c: {f: c[f] for f in ("bits", "witnessed_varying", "never_witnessed")}  # noqa: E731
    print(json.dumps({"status": record["status"], "failures": failures[:10], "witnessed_varying_bits": len(witnessed),
                      "certified": {k: brief(v) for k, v in record["certified"].items()},
                      "common_to_all_sources": brief(record["common_to_all_sources"]),
                      "beyond_common": {k: brief(v) for k, v in increments.items()},
                      "never_certified": brief(record["never_certified"])}, indent=1))
    return 0 if not failures else 1


if __name__ == "__main__":
    raise SystemExit(main())
