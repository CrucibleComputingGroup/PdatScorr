#!/usr/bin/env python3
"""Export a closed LEN5 platform model that observes every core flip-flop bit.

The platform is the existing admission-screen harness, unchanged: immutable
instruction ROM with zero fault payload, exact fetch-acceptance gap, native
two-stage fetch pipeline, three-cycle nonfaulting data service with arbitrary
load values, reset required in the initial frame and unconstrained afterwards.
The only additions are observation outputs. A new core output port aliases the
Q net of every flip-flop bit in manifest order, and a few existing core/harness
signals (native RS admission probe, fetch, store, and load requests) are also
forwarded for trace audits. No premise is added and no driver changes.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import shutil
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
sys.path.insert(0, str(REPO))
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE.parent / "application_screen"))
from odc.temporal import (checked_yosys, digest, export_design, formal_lower_command,  # noqa: E402
                          formal_prepare_command, validate_single_clock, yosys_path)
from prepare_frontend import workspace_root  # noqa: E402
from formal_screen import add_native_probes, harness  # noqa: E402
from program_rom import read_image  # noqa: E402

FF_TYPES = {"$aldff", "$adff", "$dffe", "$dff"}
OBS_PORT = "ffq_obs"
NATIVE_DATA_LATENCY = 3  # the admission-screen harness and the native memory model reply after three cycles
LATENCY_WORDS = {1: "one", 2: "two", 3: "three", 4: "four", 5: "five", 6: "six", 7: "seven", 8: "eight"}


def data_service(latency: int) -> str:
    """The harness's fully pipelined data service, replying exactly `latency` cycles after each request.

    For the native latency this is the admission-screen harness text, byte for byte. Other latencies
    change only the depth of the reply pipeline; every request is still granted and nothing is flushed.
    """
    if latency not in LATENCY_WORDS:
        raise ValueError(f"Data reply latency must be 1..{max(LATENCY_WORDS)} cycles")
    last = latency - 1
    regs = lambda prefix: [f"{prefix}{i}" for i in range(latency)]  # noqa: E731
    chain = lambda prefix, source: " ".join(  # noqa: E731
        f"{r} <= {source if i == 0 else regs(prefix)[i - 1]};" for i, r in enumerate(regs(prefix)))
    zero = lambda names: " ".join(f"{r} <= 0;" for r in names)  # noqa: E731
    shift = ((lambda v, req: f"{v} <= {{{v}[{last - 1}:0], {req}}};") if latency > 1  # noqa: E731
             else (lambda v, req: f"{v} <= {req};"))
    comment = ("" if latency == NATIVE_DATA_LATENCY else f" with {LATENCY_WORDS[latency]}-cycle replies")
    return (f"  // A fully pipelined data service{comment}; flush never cancels data replies.\n"
            f"  reg [{last}:0] lv, sv;\n"
            f"  reg [3:0] {', '.join(regs('lt') + regs('st'))};\n"
            f"  reg [63:0] {', '.join(regs('ld'))};\n"
            "  assign data_load_gnt_i = rst_ni; assign data_store_gnt_i = rst_ni;\n"
            f"  assign data_load_rvalid_i = lv[{last}]; assign data_store_rvalid_i = sv[{last}];\n"
            f"  assign data_load_tag_i = lt{last}; assign data_store_tag_i = st{last};\n"
            f"  assign data_load_rdata_i = ld{last};\n"
            "  always @(posedge clk_i) begin\n"
            "    if (!rst_ni) begin\n"
            f"      lv <= 0; sv <= 0; {zero(regs('lt'))}\n"
            f"      {zero(regs('st'))} {zero(regs('ld'))}\n"
            "    end else begin\n"
            f"      {shift('lv', 'data_load_req_o')} {shift('sv', 'data_store_req_o')}\n"
            f"      {chain('lt', 'data_load_tag_o')}\n"
            f"      {chain('st', 'data_store_tag_o')}\n"
            f"      {chain('ld', 'load_value')}\n"
            "    end\n"
            "  end\n")


def flip_flop_manifest(design: dict) -> list[dict]:
    """One record per flip-flop Q bit, ordered by cell name and bit index."""
    module = design["modules"]["datapath"]
    unsupported = sorted({c["type"] for c in module["cells"].values()
                          if re.match(r"^\$_?(?:a?l?dff|sdff|dffsr|dlatch|adlatch|sr|ff)", c["type"])} - FF_TYPES)
    if unsupported:
        raise ValueError(f"Unsupported sequential cell types: {unsupported}")
    records = []
    for name in sorted(module["cells"]):
        cell = module["cells"][name]
        kind = cell["type"]
        if kind not in FF_TYPES:
            continue
        q = cell["connections"]["Q"]
        if kind == "$aldff":
            reset = cell["connections"]["AD"]
            polarity = int(cell["parameters"]["ALOAD_POLARITY"], 2)
            control = cell["connections"]["ALOAD"]
        elif kind == "$adff":
            value = cell["parameters"]["ARST_VALUE"]
            reset = [value[len(value) - 1 - i] for i in range(len(q))]
            polarity = int(cell["parameters"]["ARST_POLARITY"], 2)
            control = cell["connections"]["ARST"]
        else:
            reset, polarity, control = [None] * len(q), None, None
        for bit, net in enumerate(q):
            if not isinstance(net, int):
                raise ValueError(f"Constant Q bit in {name}")
            value = reset[bit]
            if value is not None and value not in ("0", "1"):
                raise ValueError(f"Non-constant reset value in {name}[{bit}]")
            records.append({"cell": name, "type": kind, "bit": bit, "net": net,
                            "reset": None if value is None else int(value),
                            "reset_control": control, "reset_polarity": polarity})
    nets = [r["net"] for r in records]
    if len(set(nets)) != len(nets):
        raise ValueError("A net is driven by two flip-flop bits")
    return records


def observed_design(design: dict, records: list[dict]) -> dict:
    result = add_native_probes(design)
    module = result["modules"]["datapath"]
    if OBS_PORT in module["ports"]:
        raise ValueError("Observation port already exists")
    module["ports"][OBS_PORT] = {"direction": "output", "bits": [r["net"] for r in records]}
    return result


def closed_harness(ports: dict, gap: int, threshold: int, rom: dict,
                   data_latency: int = NATIVE_DATA_LATENCY) -> str:
    text = harness(ports, [], gap, threshold, rom, zero_fault_data=True)
    native = data_service(NATIVE_DATA_LATENCY)
    if text.count(native) != 1:
        raise ValueError("Unexpected admission-screen data service layout")
    text = text.replace(native, data_service(data_latency))
    width = len(ports[OBS_PORT]["bits"])
    index_width = len(ports["probe_index"]["bits"])
    tail = "input wire [31:0] instruction_fault_data);"
    if text.count(tail) != 1 or text.count("endmodule") != 1:
        raise ValueError("Unexpected admission-screen harness layout")
    text = text.replace(tail,
        "input wire [31:0] instruction_fault_data,\n"
        f"  output wire [{width - 1}:0] obs_ffq, output wire obs_insert, output wire [{index_width - 1}:0] obs_index,\n"
        "  output wire obs_fetch, output wire [63:0] obs_fetch_addr, output wire obs_store,\n"
        "  output wire [63:0] obs_store_addr, output wire obs_load, output wire obs_flush);")
    text = text.replace("endmodule",
        "  // Observation only: aliases of existing nets.\n"
        "  assign obs_ffq = ffq_obs; assign obs_insert = probe_insert; assign obs_index = probe_index;\n"
        "  assign obs_fetch = ipush; assign obs_fetch_addr = instr_addr_o;\n"
        "  assign obs_store = data_store_req_o; assign obs_store_addr = data_store_addr_o;\n"
        "  assign obs_load = data_load_req_o; assign obs_flush = mem_flush_o;\n"
        "endmodule")
    return text


def bare_path(path: Path) -> str:
    """write_aiger -map takes its argument verbatim, so it cannot be quoted."""
    text = str(path.resolve())
    if re.search(r'[\s"\\]', text):
        raise ValueError(f"Unsupported characters in path for write_aiger -map: {text}")
    return text


def parse_map(path: Path) -> dict:
    result = {"input": {}, "output": {}, "latch": {}, "init": {}, "bad": [], "constraint": []}
    for line in path.read_text().splitlines():
        parts = line.split()
        if not parts:
            continue
        kind = parts[0]
        if kind in ("input", "output", "latch", "init"):
            index, bit, name = int(parts[1]), int(parts[2]), parts[3]
            result[kind].setdefault(name, {})[bit] = index
        elif kind in ("bad", "constraint"):
            result[kind].append(line)
    return result


def main() -> int:
    workspace = workspace_root(HERE)
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--design", type=Path, required=True, help="Native flattened core JSON (module datapath)")
    ap.add_argument("--program-hex", type=Path, required=True)
    ap.add_argument("--gap", type=int, required=True)
    ap.add_argument("--threshold", type=int, default=1,
                    help="Native ALU RS rows below this index are asserted never admitted (sanity property)")
    ap.add_argument("--data-latency", type=int, default=NATIVE_DATA_LATENCY, choices=sorted(LATENCY_WORDS),
                    help="Fixed data reply latency in cycles (default: the native three)")
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--yosys", default=str(workspace / "tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys"))
    ap.add_argument("--timeout", type=int, default=1800)
    args = ap.parse_args()
    if args.gap < 1 or not 1 <= args.threshold <= 7:
        ap.error("Require gap >= 1 and threshold in 1..7")
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    for helper in (Path(__file__), HERE.parent / "application_screen/formal_screen.py",
                   HERE.parent / "application_screen/program_rom.py", REPO / "odc/temporal.py"):
        shutil.copyfile(helper, out / helper.name)
    shutil.copyfile(args.program_hex, out / "program.hex")
    design = json.loads(args.design.read_text())
    if set(design["modules"]) != {"datapath"}:
        raise ValueError("Expected one flattened datapath module")
    records = flip_flop_manifest(design)
    observed = observed_design(design, records)
    core = out / "core.v"
    core_export = export_design(observed, "datapath", "ObservedCore", core, args.yosys, args.timeout)
    rom = read_image(args.program_hex)
    platform = out / "ClosedPlatform.sv"
    platform.write_text(closed_harness(observed["modules"]["datapath"]["ports"], args.gap, args.threshold, rom,
                                       args.data_latency))
    record = {
        "status": "running",
        "scope": ("Closed native platform model for ternary reachability: immutable ROM, zero fault payload, "
                  f"exact fetch-acceptance gap, {LATENCY_WORDS[args.data_latency]}-cycle nonfaulting data service "
                  "with arbitrary load values"),
        "data_reply_latency": args.data_latency,
        "design": str(args.design.resolve()), "design_sha256": digest(args.design),
        "program_hex_sha256": digest(args.program_hex), "rom_image_sha256": rom["image_sha256"],
        "instruction_acceptance_gap": args.gap, "instruction_fault_payload": "zero",
        "admission_threshold_property": args.threshold,
        "reset_model": "reset asserted in the initial frame, unconstrained afterwards ($initstate -> !rst_ni)",
        "flip_flop_bits": len(records),
        "flip_flop_types": {k: sum(r["type"] == k for r in records) for k in sorted(FF_TYPES)},
        "core_export": core_export, "core_json_sha256": digest(core.with_suffix(".json")),
        "platform_sha256": digest(platform),
        "helpers_sha256": {p.name: digest(out / p.name) for p in (
            Path("export_closed.py"), Path("formal_screen.py"), Path("program_rom.py"), Path("temporal.py"))},
    }
    (out / "summary.json").write_text(json.dumps(record, indent=2) + "\n")
    record["prepare"] = checked_yosys(args.yosys,
        f"read_json {yosys_path(core.with_suffix('.json'))}\nrename datapath ObservedCore\n"
        "bwmuxmap\nbmuxmap\ndemuxmap\n"
        f"read_verilog -formal -sv {yosys_path(platform)}\n"
        + formal_prepare_command("AdmissionScreen") + formal_lower_command(args.yosys)
        + "select -assert-count 3 t:$assert\nselect -assert-count 1 t:$assume\nselect *\n"
        "memory_map\nsetundef -anyseq\nopt_clean\nasync2sync\ndffunmap\nsetundef -anyseq\n"
        f"write_json {yosys_path(out / 'screen.json')}\n", out, "prepare", args.timeout)
    model = json.loads((out / "screen.json").read_text())
    record["clock_model"] = validate_single_clock(model, "AdmissionScreen")
    record["screen_json_sha256"] = digest(out / "screen.json")
    record["export"] = checked_yosys(args.yosys,
        f"read_json {yosys_path(out / 'screen.json')}\n"
        "formalff -clk2ff\nsetundef -anyseq\nopt -keepdc\ntechmap\nopt -keepdc\nsetundef -anyseq\naigmap\n"
        f"write_aiger -zinit -symbols -map {bare_path(out / 'screen.aigmap')} {yosys_path(out / 'screen.aig')}\n",
        out, "export", args.timeout)
    with (out / "screen.aig").open("rb") as f:
        header = f.readline().decode().split()
    if header[0] != "aig" or int(header[6]) != 3 or int(header[7]) != 1:
        raise ValueError(f"Unexpected AIG header {header}")
    symbols = parse_map(out / "screen.aigmap")
    if set(symbols["input"].get("rst_ni", {})) != {0}:
        raise ValueError("Reset input not found in AIG map")
    ffq = symbols["output"].get("obs_ffq", {})
    if sorted(ffq) != list(range(len(records))):
        raise ValueError("Observation output bits are incomplete in the AIG map")
    for i, r in enumerate(records):
        r["aig_output"] = ffq[i]
    observation = {name: [bits[b] for b in sorted(bits)] for name, bits in symbols["output"].items() if name != "obs_ffq"}
    (out / "manifest.json").write_text(json.dumps({"records": records, "observation_outputs": observation,
                                                   "reset_input_index": symbols["input"]["rst_ni"][0]}) + "\n")
    record.update(status="exported", aig_header=header, aig_sha256=digest(out / "screen.aig"),
                  aig_map_sha256=digest(out / "screen.aigmap"), manifest_sha256=digest(out / "manifest.json"),
                  reset_input_index=symbols["input"]["rst_ni"][0])
    (out / "summary.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({k: record[k] for k in ("status", "aig_header", "flip_flop_bits", "reset_input_index")}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
