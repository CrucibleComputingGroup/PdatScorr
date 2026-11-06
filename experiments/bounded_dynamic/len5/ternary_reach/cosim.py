#!/usr/bin/env python3
"""Independent co-simulation of the original and constant-substituted LEN5 cores.

Verilator runs the original core and every substituted core, each re-exported here
from its netlist with the same observation outputs and placed in its own copy of
the closed platform harness, under identical stimuli: reset in the first cycle,
random re-resets, random or program-image load values, and random values on the
remaining platform inputs. The harness text is the formal model's without its
$initstate premise and its assertions; the testbench checks those assertions.
Flip-flops without reset and the harness registers start from the same random
value in every copy. All other state starts random in each copy and is then reset.

Every cycle from the first reset on, the testbench checks that every constant
certified for this platform holds in the original core, that the platform's
assertions hold, and that each substituted core whose constants are certified for
this platform matches the original on every core output and every flip-flop bit.
Substituted cores certified only for other platforms run as negative controls.
Image runs (program data, no re-reset) also compare the original core's accepted
stores with the recorded native RTL platform simulation.

This is finite simulation evidence. It does not replace the ternary invariant.
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
from export_closed import OBS_PORT, flip_flop_manifest, observed_design  # noqa: E402
from prepare_frontend import workspace_root  # noqa: E402

PROBES = ("probe_insert", "probe_index", OBS_PORT)
ASSUME = "  always @* if ($initstate) assume (!rst_ni);\n"
ASSERTS = re.compile(r"  // These are proof obligations, never premises on internal service\.\n"
                     r"  always @\* if \(rst_ni\) begin\n((?:    assert \([^\n]*\);\n)+)  end\n")
PORT_TAIL = "output wire obs_load, output wire obs_flush);"
NAME = r"\\\S+ |[A-Za-z_]\w*"
NO_RESET_FF = re.compile(
    r"  always @\(posedge clk_i\)\n"
    rf"    (?:if \([^\n]*?\) )?(?P<q>{NAME}) <= [^\n]*;\n"
    rf"  assign {OBS_PORT}\[(?P<hi>\d+)(?::(?P<lo>\d+))?\] = (?P<q2>{NAME});\n")


def replace_once(text: str, old: str, new: str) -> str:
    if text.count(old) != 1:
        raise ValueError(f"Expected exactly one occurrence of {old!r}")
    return text.replace(old, new)


def harness_registers(text: str) -> list[tuple[str, int]]:
    regs = []
    for m in re.finditer(r"\breg (?:\[(\d+):(\d+)\] )?([A-Za-z_]\w*(?:, *[A-Za-z_]\w*)*);", text):
        width = int(m.group(1)) - int(m.group(2)) + 1 if m.group(1) else 1
        for name in re.split(r", *", m.group(3)):
            if not name.startswith("selected_"):  # combinational
                regs.append((name, width))
    return regs


def sim_platform(text: str, instance: str, core_module: str, outputs: list[tuple[str, int]]) -> tuple[str, dict]:
    """The formal harness without its premise and assertions, plus observation outputs."""
    blocks = list(ASSERTS.finditer(text))
    if len(blocks) != 1:
        raise ValueError("Unexpected assertion block layout")
    asserts = re.findall(r"assert \((.*)\);", blocks[0].group(1))
    admission = [a for a in asserts if "probe_index" in a]
    service = [a for a in asserts if "probe_index" not in a]
    m = re.fullmatch(r"!\(probe_insert && probe_index < 3'd(\d)\)", admission[0]) if len(admission) == 1 else None
    if m is None or len(service) != 2:
        raise ValueError(f"Unexpected assertions {asserts}")
    regs = harness_registers(text)
    for name, width in outputs:
        if f"  wire [{width - 1}:0] {name};\n" not in text:
            raise ValueError(f"Harness has no wire for core output {name}")
    text = replace_once(text, ASSUME, "")
    text = replace_once(text, blocks[0].group(0), "")
    text = replace_once(text, "module AdmissionScreen(", f"module Platform_{instance}(")
    text = replace_once(text, "  ObservedCore dut(", f"  {core_module} dut(")
    width = sum(w for _, w in outputs)
    text = replace_once(text, PORT_TAIL,
        "output wire obs_load, output wire obs_flush,\n"
        f"  output wire [{width - 1}:0] obs_core, output wire [63:0] obs_load_addr, output wire [63:0] obs_store_data,\n"
        "  output wire [7:0] obs_store_be, output wire obs_service_ok);")
    extra = ("  // Co-simulation only: observation aliases and shared initial register values.\n"
             f"  assign obs_core = {{{', '.join(n for n, _ in outputs)}}};\n"
             "  assign obs_load_addr = data_load_addr_o; assign obs_store_data = data_store_wdata_o;\n"
             "  assign obs_store_be = data_store_be_o;\n"
             f"  assign obs_service_ok = {' && '.join(f'({a})' for a in service)};\n"
             "  initial begin\n"
             + "".join(f"    if (!$value$plusargs(\"pinit_{n}=%h\", {n})) {n} = '0;\n" for n, _ in regs)
             + "  end\nendmodule")
    text = replace_once(text, "endmodule", extra)
    return text, {"admission_threshold": int(m.group(1)), "service_assertions": service, "registers": regs}


def seed_no_reset_flip_flops(text: str, records: list[dict]) -> tuple[str, list[tuple[int, int]]]:
    """Make each flip-flop without reset take its initial value from a shared plusarg."""
    ranges = []

    def insert(m: re.Match) -> str:
        if m.group("q") != m.group("q2"):
            raise ValueError(f"Unexpected no-reset flip-flop layout at {m.group(0)!r}")
        hi = int(m.group("hi"))
        lo = int(m.group("lo")) if m.group("lo") is not None else hi
        ranges.append((lo, hi - lo + 1))
        q = m.group("q")
        return m.group(0) + f"  initial if (!$value$plusargs(\"finit_{lo}=%h\", {q})) {q} = '0;\n"

    result = NO_RESET_FF.sub(insert, text)
    expected = sorted(i for i, r in enumerate(records) if r["reset"] is None)
    covered = sorted(i for lo, w in ranges for i in range(lo, lo + w))
    if text.count("  always @(posedge clk_i)\n") != len(ranges) or covered != expected:
        raise ValueError("No-reset flip-flops in the exported Verilog do not match the manifest")
    return result, sorted(ranges)


def data_image(path: Path) -> tuple[int, list[int]]:
    mem, addr = {}, None
    for token in path.read_text().split():
        if token.startswith("@"):
            addr = int(token[1:], 16)
        else:
            mem[addr] = int(token, 16)
            addr += 1
    base, end = min(mem) & ~7, (max(mem) | 7) + 1
    return base, [sum(mem.get(base + 8 * i + k, 0) << (8 * k) for k in range(8)) for i in range((end - base) // 8)]


def hex_vector(bits: list[int]) -> str:
    value = sum(b << i for i, b in enumerate(bits))
    return f"{len(bits)}'h{value:0{(len(bits) + 3) // 4}x}"


TESTBENCH = r"""// Generated by cosim.py.
module tb;
  localparam int W = @W@;
  localparam int K = @K@;
  localparam int NV = @NV@;
  localparam int THRESHOLD = @THRESHOLD@;
  localparam logic [W-1:0] CMASK = @CMASK@;
  localparam logic [W-1:0] CVAL = @CVAL@;
  localparam logic [63:0] IMG_BASE = 64'h@IMG_BASE@;
  localparam int IMG_WORDS = @IMG_WORDS@;
  logic clk = 1'b0, rst_ni = 1'b1, image_mode = 1'b0;
  logic [3:0] instruction_choice = '0;
  logic [63:0] random_load = '0;
  logic [2:0] invalid_code_nonzero = '0;
  logic [31:0] instruction_fault_data = '0;
  logic [63:0] image [0:IMG_WORDS-1];
  wire [63:0] load_value;
  wire [W-1:0] o_ffq; wire [K-1:0] o_core; wire o_insert; wire [2:0] o_index; wire o_fetch;
  wire [63:0] o_fetch_addr; wire o_store; wire [63:0] o_store_addr; wire o_load; wire o_flush;
  wire [63:0] o_load_addr, o_store_data; wire [7:0] o_store_be; wire o_service_ok;
  Platform_orig orig(.clk_i(clk), .rst_ni(rst_ni), .instruction_choice(instruction_choice),
    .load_value(load_value), .invalid_code_nonzero(invalid_code_nonzero),
    .instruction_fault_data(instruction_fault_data), .obs_ffq(o_ffq), .obs_insert(o_insert),
    .obs_index(o_index), .obs_fetch(o_fetch), .obs_fetch_addr(o_fetch_addr), .obs_store(o_store),
    .obs_store_addr(o_store_addr), .obs_load(o_load), .obs_flush(o_flush), .obs_core(o_core),
    .obs_load_addr(o_load_addr), .obs_store_data(o_store_data), .obs_store_be(o_store_be),
    .obs_service_ok(o_service_ok));
@INSTANCES@
  function automatic logic [63:0] image_word(input logic [63:0] addr);
    logic [63:0] offset;
    offset = addr - IMG_BASE;
    if (addr < IMG_BASE || (offset >> 3) >= 64'(IMG_WORDS)) return 64'h0;
    return image[offset[31:3]];
  endfunction
  assign load_value = image_mode ? image_word(o_load_addr) : random_load;

  function automatic logic [63:0] fold(input logic [K-1:0] v);
    logic [63:0] r;
    r = '0;
    for (int i = 0; i < K; i += 64) r ^= 64'(v >> i);
    return r;
  endfunction

  int unsigned cycles, reset_period, hold, image_arg;
  int cyc, fd;
  string path;
  longint unsigned const_fail, prop_fail, service_fail, fetches, stores, loads, flushes;
  longint unsigned reset_frames, rereset_events, reset_admissions;
  longint first_const_fail, first_prop_fail, first_service_fail;
  longint unsigned adm [0:7];
  longint unsigned mism [0:NV-1];
  longint first_mism [0:NV-1];
  logic [63:0] trace_digest;

  task automatic report_bits(input string kind, input int v, input logic [W-1:0] ffq_diff,
                             input logic [K-1:0] core_diff);
    int n;
    n = 0;
    for (int i = 0; i < W && n < 16; i++) if (ffq_diff[i]) begin
      $display("COSIM_BIT %s %0d %0d ffq %0d", kind, v, cyc, i); n++;
    end
    n = 0;
    for (int i = 0; i < K && n < 16; i++) if (core_diff[i]) begin
      $display("COSIM_BIT %s %0d %0d core %0d", kind, v, cyc, i); n++;
    end
  endtask

  task automatic check();
    logic [W-1:0] violation;
    if (!rst_ni) reset_frames++;
    violation = (o_ffq ^ CVAL) & CMASK;
    if (violation != '0) begin
      const_fail++;
      if (first_const_fail < 0) begin
        first_const_fail = cyc;
        report_bits("const", -1, violation, '0);
      end
    end
    if (rst_ni) begin
      if (o_insert) begin
        adm[o_index]++;
        if (32'(o_index) < THRESHOLD) begin
          prop_fail++;
          if (first_prop_fail < 0) first_prop_fail = cyc;
        end
      end
      if (!o_service_ok) begin
        service_fail++;
        if (first_service_fail < 0) first_service_fail = cyc;
      end
      if (o_fetch) fetches++;
      if (o_load) loads++;
      if (o_flush) flushes++;
      if (o_store) begin
        stores++;
        if (fd != 0) $fwrite(fd, "%0d,%0d,%0d,%0d\n", cyc, o_store_addr, o_store_data, o_store_be);
      end
    end else if (o_insert) reset_admissions++;
    trace_digest = {trace_digest[62:0], trace_digest[63]} ^ fold(o_core) ^ 64'(cyc);
@CHECKS@
  endtask

  initial begin
    if (!$value$plusargs("cycles=%d", cycles)) cycles = 20000;
    if (!$value$plusargs("reset_period=%d", reset_period)) reset_period = 0;
    if (!$value$plusargs("image=%d", image_arg)) image_arg = 0;
    image_mode = image_arg != 0;
    fd = 0;
    if ($value$plusargs("store_log=%s", path)) fd = $fopen(path, "w");
    if (image_mode) begin
      if (!$value$plusargs("image_file=%s", path)) $fatal(1, "image_file plusarg required");
      $readmemh(path, image);
    end
    {const_fail, prop_fail, service_fail, fetches, stores, loads, flushes} = '0;
    {reset_frames, rereset_events, reset_admissions} = '0;
    first_const_fail = -1; first_prop_fail = -1; first_service_fail = -1;
    for (int i = 0; i < 8; i++) adm[i] = 0;
    for (int v = 0; v < NV; v++) begin mism[v] = 0; first_mism[v] = -1; end
    trace_digest = '0;
    hold = 0;
    #2;
    for (cyc = 0; cyc < int'(cycles); cyc++) begin
      // Inputs of this cycle; the clock is low.
      if (cyc == 0) begin rst_ni = 1'b0; hold = $urandom % 3; end
      else if (hold > 0) begin rst_ni = 1'b0; hold--; end
      else if (reset_period > 0 && $urandom % reset_period == 0) begin
        rst_ni = 1'b0; hold = $urandom % 4; rereset_events++;
      end else rst_ni = 1'b1;
      instruction_choice = 4'($urandom);
      invalid_code_nonzero = 3'($urandom);
      instruction_fault_data = $urandom;
      case ($urandom % 8)
        0: random_load = 64'h0;
        1: random_load = '1;
        2: random_load = 64'h8000_0000_0000_0000;
        3: random_load = 64'($urandom % 16);
        default: random_load = {$urandom, $urandom};
      endcase
      #4;
      check();
      #1 clk = 1'b1;
      #4 clk = 1'b0;
      #1;
    end
    if (fd != 0) $fclose(fd);
    $display("COSIM simulated_cycles %0d", cyc);
    $display("COSIM image_mode %0d", image_arg);
    $display("COSIM reset_period_arg %0d", reset_period);
    $display("COSIM reset_frames %0d", reset_frames);
    $display("COSIM rereset_events %0d", rereset_events);
    $display("COSIM fetches %0d", fetches);
    $display("COSIM loads %0d", loads);
    $display("COSIM stores %0d", stores);
    $display("COSIM flushes %0d", flushes);
    $display("COSIM reset_admissions %0d", reset_admissions);
    $display("COSIM const_fail %0d %0d", const_fail, first_const_fail);
    $display("COSIM prop_fail %0d %0d", prop_fail, first_prop_fail);
    $display("COSIM service_fail %0d %0d", service_fail, first_service_fail);
    for (int i = 0; i < 8; i++) $display("COSIM adm %0d %0d", i, adm[i]);
    for (int v = 0; v < NV; v++) $display("COSIM mism %0d %0d %0d", v, mism[v], first_mism[v]);
    $display("COSIM digest %016x", trace_digest);
    $finish;
  end
endmodule
"""

INSTANCE = r"""  wire [W-1:0] v@I@_ffq; wire [K-1:0] v@I@_core;
  Platform_@NAME@ v@I@(.clk_i(clk), .rst_ni(rst_ni), .instruction_choice(instruction_choice),
    .load_value(load_value), .invalid_code_nonzero(invalid_code_nonzero),
    .instruction_fault_data(instruction_fault_data), .obs_ffq(v@I@_ffq), .obs_core(v@I@_core),
    .obs_insert(), .obs_index(), .obs_fetch(), .obs_fetch_addr(), .obs_store(), .obs_store_addr(),
    .obs_load(), .obs_flush(), .obs_load_addr(), .obs_store_data(), .obs_store_be(), .obs_service_ok());
"""

CHECK = r"""    if (v@I@_ffq != o_ffq || v@I@_core != o_core) begin
      mism[@I@]++;
      if (first_mism[@I@] < 0) begin
        first_mism[@I@] = cyc;
        report_bits("mism", @I@, v@I@_ffq ^ o_ffq, v@I@_core ^ o_core);
      end
    end
"""


def fill(template: str, **values) -> str:
    for key, value in values.items():
        template = template.replace(f"@{key}@", str(value))
    if re.search(r"@[A-Z_]+@", template):
        raise ValueError("Unfilled template field")
    return template


def parse_result(stdout: str) -> dict:
    result = {"adm": {}, "mism": {}, "bits": []}
    for line in stdout.splitlines():
        parts = line.split()
        if not parts:
            continue
        if parts[0] == "COSIM":
            key, values = parts[1], parts[2:]
            if key == "adm":
                result["adm"][int(values[0])] = int(values[1])
            elif key == "mism":
                result["mism"][int(values[0])] = {"cycles": int(values[1]), "first": int(values[2])}
            elif key == "digest":
                result["digest"] = values[0]
            elif len(values) == 2:
                result[key] = {"cycles": int(values[0]), "first": int(values[1])}
            else:
                result[key] = int(values[0])
        elif parts[0] == "COSIM_BIT":
            result["bits"].append({"kind": parts[1], "variant": int(parts[2]), "cycle": int(parts[3]),
                                   "vector": parts[4], "index": int(parts[5])})
    return result


def main() -> int:
    workspace = workspace_root(HERE)
    bin_dir = workspace / "tools/oss-cad-suite-20261104/oss-cad-suite/bin"
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--model", type=Path, required=True, help="export_closed.py output (the platform)")
    ap.add_argument("--reach", type=Path, required=True, help="reach.py output for this model")
    ap.add_argument("--variant", action="append", required=True, metavar="NAME=SUBSTITUTE_DIR")
    ap.add_argument("--evidence", type=Path, required=True, help="Recorded RTL platform simulation evidence")
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--seeds", type=int, default=16)
    ap.add_argument("--cycles", type=int, default=20000)
    ap.add_argument("--reset-periods", type=int, nargs="+", default=[300, 1000, 3000, 0],
                    help="Mean cycles between random re-resets, cycled over seeds (0: none)")
    ap.add_argument("--image-seeds", type=int, default=2)
    ap.add_argument("--x-assign", choices=("0", "1"), default="0",
                    help="Value of explicit X constants (identical in every core copy)")
    ap.add_argument("--yosys", default=str(bin_dir / "yosys"))
    ap.add_argument("--verilator", default=str(bin_dir / "verilator"))
    ap.add_argument("--jobs", type=int, default=min(64, os.cpu_count() or 1))
    ap.add_argument("--timeout", type=int, default=7200)
    args = ap.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    shutil.copyfile(Path(__file__), out / "cosim.py")
    model = args.model.resolve()
    summary = json.loads((model / "summary.json").read_text())
    if summary.get("status") != "exported" or digest(model / "ClosedPlatform.sv") != summary["platform_sha256"]:
        raise ValueError("Model directory does not match its export record")
    reach = json.loads((args.reach / "summary.json").read_text())
    constants = json.loads((args.reach / "constants.json").read_text())
    if reach.get("status") != "certified" or reach["model_aig_sha256"] != summary["aig_sha256"] \
            or constants["status"] != "certified" or digest(args.reach / "constants.json") != reach["constants_sha256"]:
        raise ValueError("Reachability result is not a certified run of this model")
    program = args.evidence / "instruction.hex"
    if digest(program) != digest(model / "program.hex"):
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
    mask, value = [0] * len(records), [0] * len(records)
    for c in constants["constants"]:
        i = index[(c["cell"], c["bit"])]
        mask[i], value[i] = 1, c["value"]

    cores = [("orig", original, None)]
    variants = []
    for spec in args.variant:
        name, _, path = spec.partition("=")
        if not re.fullmatch(r"[a-z][a-z0-9]*", name) or name == "orig" or not path:
            ap.error(f"Bad --variant {spec}")
        sdir = Path(path).resolve()
        ssum = json.loads((sdir / "summary.json").read_text())
        if ssum.get("status") != "substituted" or ssum["design_sha256"] != summary["design_sha256"] \
                or digest(sdir / "design.json") != ssum["output_design_sha256"]:
            raise ValueError(f"{sdir} is not a substitution of this design")
        certified = summary["aig_sha256"] in {s["model_aig_sha256"] for s in ssum["constant_sources"]}
        design = json.loads((sdir / "design.json").read_text())
        vrecords = flip_flop_manifest(design)
        if vrecords != records:
            raise ValueError(f"{name}: flip-flops differ from the original")
        variants.append({"name": name, "substitute": str(sdir), "substitute_summary_sha256": digest(sdir / "summary.json"),
                         "design_sha256": ssum["output_design_sha256"], "applied_constant_bits": ssum["applied_constant_bits"],
                         "constant_sources": [{"gap": s["gap"], "model_aig_sha256": s["model_aig_sha256"]}
                                              for s in ssum["constant_sources"]],
                         "certified_for_this_platform": certified,
                         "role": "equivalence check" if certified else "negative control"})
        cores.append((name, design, vrecords))

    platform_text = (model / "ClosedPlatform.sv").read_text()
    files, outputs, layout, platform_info, no_reset = [], None, None, None, None
    for name, design, _ in cores:
        observed = observed_design(design, records)
        ports = observed["modules"]["datapath"]["ports"]
        core_outputs = sorted((n, len(p["bits"])) for n, p in ports.items()
                              if p["direction"] == "output" and n not in PROBES)
        if outputs is None:
            outputs = core_outputs
        elif core_outputs != outputs:
            raise ValueError(f"{name}: core output ports differ")
        verilog = out / f"core_{name}.v"
        export_design(observed, "datapath", f"Core_{name}", verilog, args.yosys, args.timeout)
        if name == "orig" and digest(verilog.with_suffix(".json")) != summary["core_json_sha256"]:
            raise ValueError("Original observed core differs from the formal model's core")
        text, ranges = seed_no_reset_flip_flops(verilog.read_text(), records)
        if no_reset is None:
            no_reset = ranges
        elif ranges != no_reset:
            raise ValueError(f"{name}: no-reset flip-flops differ")
        sim_core = out / f"sim_core_{name}.v"
        sim_core.write_text(text)
        ptext, info = sim_platform(platform_text, name, f"Core_{name}", outputs)
        if platform_info is None:
            platform_info = info
        (out / f"platform_{name}.sv").write_text(ptext)
        files += [sim_core, out / f"platform_{name}.sv"]
    layout, low = [], 0
    for name, width in reversed(outputs):  # concatenation: last port in the least significant bits
        layout.append({"port": name, "lsb": low, "width": width})
        low += width
    total = low
    base, words = data_image(args.evidence / "data.hex")
    (out / "image.hex").write_text("".join(f"{w:016x}\n" for w in words))
    tb = fill(TESTBENCH, W=len(records), K=total, NV=len(variants), THRESHOLD=platform_info["admission_threshold"],
              CMASK=hex_vector(mask), CVAL=hex_vector(value), IMG_BASE=f"{base:x}", IMG_WORDS=len(words),
              INSTANCES="".join(fill(INSTANCE, I=i, NAME=v["name"]) for i, v in enumerate(variants)),
              CHECKS="".join(fill(CHECK, I=i) for i, v in enumerate(variants)))
    (out / "tb.sv").write_text(tb)
    files.append(out / "tb.sv")

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
        "model": str(model), "model_aig_sha256": summary["aig_sha256"], "gap": summary["instruction_acceptance_gap"],
        "reach": str(args.reach.resolve()), "constants_sha256": digest(args.reach / "constants.json"),
        "checked_constant_bits": sum(mask), "design_sha256": summary["design_sha256"],
        "evidence": str(args.evidence.resolve()), "data_image_sha256": digest(args.evidence / "data.hex"),
        "variants": variants, "flip_flop_bits": len(records), "core_output_bits": total, "core_outputs": layout,
        "no_reset_flip_flops": [{"ffq_lsb": lo, "width": w} for lo, w in no_reset],
        "harness": {"admission_threshold": platform_info["admission_threshold"],
                    "service_assertions": platform_info["service_assertions"],
                    "shared_initial_registers": [n for n, _ in platform_info["registers"]]},
        "verilator": version, "x_assign": args.x_assign,
        "build": {"argv": argv, "returncode": build.returncode, "seconds": round(time.time() - start, 1),
                  "log_sha256": digest(out / "build.log")},
        "sources_sha256": {f.name: digest(f) for f in files + [out / "image.hex"]},
        "script_sha256": digest(Path(__file__)),
    }
    (out / "summary.json").write_text(json.dumps(record, indent=2) + "\n")
    if build.returncode != 0:
        raise RuntimeError("Verilator build failed; see build.log")

    expected_stores = [((int(r["time"]) - 1) // 2, int(r["data_store_addr_o"]), int(r["data_store_wdata_o"]),
                        int(r["data_store_be_o"])) for r in csv.DictReader((args.evidence / "accepted_stores.csv").open())]
    runs = []
    for s in range(args.seeds):
        runs.append({"seed": s + 1, "image": False, "cycles": args.cycles,
                     "reset_period": args.reset_periods[s % len(args.reset_periods)]})
    for s in range(args.image_seeds):
        runs.append({"seed": 1001 + s, "image": True, "cycles": expected_stores[-1][0] + 1000, "reset_period": 0})

    def execute(run: dict) -> dict:
        rng = random.Random(run["seed"])
        plus = [f"+finit_{lo}={rng.getrandbits(w):x}" for lo, w in no_reset]
        plus += [f"+pinit_{n}={rng.getrandbits(w):x}" for n, w in platform_info["registers"]]
        tag = f"{'image' if run['image'] else 'random'}_{run['seed']}"
        argv = [str(out / "obj/simv"), f"+verilator+seed+{run['seed']}", "+verilator+rand+reset+2",
                f"+cycles={run['cycles']}", f"+reset_period={run['reset_period']}", f"+image={int(run['image'])}"]
        if run["image"]:
            argv += [f"+image_file={out / 'image.hex'}", f"+store_log={out / (tag + '.stores.csv')}"]
        t0 = time.time()
        proc = subprocess.run(argv + plus, env=env, capture_output=True, text=True, timeout=args.timeout)
        (out / f"{tag}.log").write_text(proc.stdout + proc.stderr)
        result = parse_result(proc.stdout)
        result.update(run, returncode=proc.returncode, seconds=round(time.time() - t0, 1),
                      log_sha256=digest(out / f"{tag}.log"))
        for b in result["bits"]:
            if b["vector"] == "ffq":
                r = records[b["index"]]
                b["name"] = f"{r['cell']}[{r['bit']}]"
            else:
                port = next(p for p in layout if p["lsb"] <= b["index"] < p["lsb"] + p["width"])
                b["name"] = f"{port['port']}[{b['index'] - port['lsb']}]"
        if run["image"]:
            got = [tuple(int(x) for x in line.split(",")) for line in
                   (out / f"{tag}.stores.csv").read_text().splitlines()]
            shifts = {e[0] - g[0] for e, g in zip(expected_stores, got)}
            result["image_stores"] = {
                "recorded": len(expected_stores), "simulated": len(got),
                "values_match": [g[1:] for g in got] == [e[1:] for e in expected_stores],
                "cycle_shifts": sorted(shifts), "store_log_sha256": digest(out / f"{tag}.stores.csv")}
        return result

    with concurrent.futures.ThreadPoolExecutor(max_workers=min(len(runs), args.jobs)) as pool:
        results = list(pool.map(execute, runs))
    failures = []
    for r in results:
        where = f"seed {r['seed']}"
        if r["returncode"] != 0 or "digest" not in r or r.get("simulated_cycles") != r["cycles"] \
                or r.get("image_mode") != int(r["image"]) or r.get("reset_period_arg") != r["reset_period"]:
            failures.append(f"{where}: simulation did not finish")
            continue
        for key in ("const_fail", "prop_fail", "service_fail"):
            if r[key]["cycles"]:
                failures.append(f"{where}: {key} at cycle {r[key]['first']}")
        for i, v in enumerate(variants):
            if v["certified_for_this_platform"] and r["mism"][i]["cycles"]:
                failures.append(f"{where}: {v['name']} differs from the original at cycle {r['mism'][i]['first']}")
        if r["fetches"] == 0 or r["stores"] == 0:
            failures.append(f"{where}: no activity")
        if r["image"]:
            st = r["image_stores"]
            if not st["values_match"] or len(st["cycle_shifts"]) != 1:
                failures.append(f"{where}: stores differ from the recorded RTL simulation")
        elif r["reset_period"] and not r["rereset_events"]:
            failures.append(f"{where}: no re-reset occurred")
    controls = {}
    for i, v in enumerate(variants):
        if not v["certified_for_this_platform"]:
            diverged = [r for r in results if r["mism"][i]["cycles"]]
            controls[v["name"]] = {"runs": len(results), "diverged_runs": len(diverged),
                                   "first_divergence_cycles": [r["mism"][i]["first"] for r in diverged][:8]}
    admissions = {k: sum(r["adm"][k] for r in results) for k in range(8)}
    record.update(
        status="passed" if not failures else "failed", failures=failures, runs=results,
        totals={"runs": len(results), "cycles": sum(r["cycles"] for r in results),
                "rereset_events": sum(r["rereset_events"] for r in results),
                "alu_rs_admissions_by_row": admissions,
                "constant_violation_cycles": sum(r["const_fail"]["cycles"] for r in results),
                "admission_property_violation_cycles": sum(r["prop_fail"]["cycles"] for r in results),
                "service_assertion_violation_cycles": sum(r["service_fail"]["cycles"] for r in results),
                "equivalence_mismatch_cycles": {v["name"]: sum(r["mism"][i]["cycles"] for r in results)
                                                for i, v in enumerate(variants)},
                "distinct_trace_digests": len({r["digest"] for r in results})},
        negative_controls=controls)
    (out / "summary.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({k: record[k] for k in ("status", "gap", "failures", "totals", "negative_controls")}, indent=1))
    return 0 if not failures else 1


if __name__ == "__main__":
    raise SystemExit(main())
