#!/usr/bin/env python3
"""Screen an RS admission bound on original LEN5 under external service rules.

Instruction replies nondeterministically choose a word from the streaming
kernel's instruction alphabet. This defines an alphabet domain; it is not an
exact instruction ROM model. The recorded kernel trace fits this domain, but
unbounded inclusion of all its speculative fetches is not established. The
query does NOT assume a PC sequence, operand readiness, occupancy, or issue
rate. Memory supplies arbitrary load values. A counterexample need not be a
legal trace of that exact kernel.
This is a safety query, not an optimizer or an accepted replacement design.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
sys.path.insert(0, str(REPO))
sys.path.insert(0, str(HERE.parent))
from odc.temporal import checked_yosys, digest, export_design, formal_lower_command, run_command, validate_single_clock, yosys_path
from prepare_frontend import PRE_FPU_PIN, workspace_root


def harness(ports, instructions, gap, threshold):
    lines = ["module AdmissionScreen(input wire clk_i, rst_ni,",
             "  input wire [3:0] instruction_choice, input wire [63:0] load_value,",
             "  input wire [2:0] invalid_code_nonzero);",
             "  always @* if ($initstate) assume (!rst_ni);"]
    widths = {n:len(p["bits"]) for n,p in ports.items()}
    for name, width in widths.items():
        if name not in ("clk_i", "rst_ni"):
            lines.append(f"  wire [{width-1}:0] {name};")
    lines += ["  ObservedCore dut(" + ",".join(f".{n}({n})" for n in ports) + ");",
              "  reg [31:0] selected_instruction;",
              "  always @* begin", "    selected_instruction = 32'h00000013;",
              "    case (instruction_choice)"]
    if len(instructions) > 16:
        raise ValueError("The v1 alphabet selector supports at most 16 instructions")
    for index, word in enumerate(instructions):
        lines.append(f"      4'd{index}: selected_instruction = 32'h{word:08x};")
    lines += ["      default: ;", "    endcase", "  end",
        "  assign irq_i = 0;", "  assign fetch_enable_i = 1;",
        "  assign instr_except_raised_i = 0;",
        "  assign instr_except_code_i = (instr_rvalid_i || invalid_code_nonzero[0]) ? 31 : 0;",
        "  assign data_load_except_raised_i = 0;",
        "  assign data_load_except_code_i = (data_load_rvalid_i || invalid_code_nonzero[1]) ? 31 : 0;",
        "  assign data_store_except_raised_i = 0;",
        "  assign data_store_except_code_i = (data_store_rvalid_i || invalid_code_nonzero[2]) ? 31 : 0;",
        "  // Native two-stage fetch pipeline: freeze with core response readiness.",
        "  // SKIP_INS_ANS_REG=1 couples upstream grant to this same readiness.",
        "  reg [1:0] iv; reg [31:0] ins0, ins1;",
        f"  reg [{max(1,(gap-1).bit_length())-1}:0] gap_left;",
        "  wire gate_open = gap_left == 0;",
        "  wire ipush = instr_req_o && instr_gnt_i;",
        "  assign instr_gnt_i = instr_rready_o && gate_open;",
        "  assign instr_rvalid_i = iv[1];",
        "  assign instr_rdata_i = ins1;",
        "  always @(posedge clk_i) begin",
        "    if (!rst_ni) begin",
        "      iv <= 0; ins0 <= 0; ins1 <= 0; gap_left <= 0;",
        "    end else begin",
        "      if (gap_left != 0) gap_left <= gap_left - 1;",
        f"      if (ipush) gap_left <= {gap-1};",
        "      if (mem_flush_o) begin iv <= 0; ins0 <= 0; ins1 <= 0; end",
        "      else if (instr_rready_o) begin",
        "        iv <= {iv[0], instr_req_o && gate_open};",
        "        ins0 <= (instr_req_o && gate_open) ? selected_instruction : 0;",
        "        ins1 <= ins0;",
        "      end",
        "    end",
        "  end",
        "  // A fully pipelined data service; flush never cancels data replies.",
        "  reg [2:0] lv, sv;",
        "  reg [3:0] lt0, lt1, lt2, st0, st1, st2;",
        "  reg [63:0] ld0, ld1, ld2;",
        "  assign data_load_gnt_i = rst_ni; assign data_store_gnt_i = rst_ni;",
        "  assign data_load_rvalid_i = lv[2]; assign data_store_rvalid_i = sv[2];",
        "  assign data_load_tag_i = lt2; assign data_store_tag_i = st2;",
        "  assign data_load_rdata_i = ld2;",
        "  always @(posedge clk_i) begin",
        "    if (!rst_ni) begin",
        "      lv <= 0; sv <= 0; lt0 <= 0; lt1 <= 0; lt2 <= 0;",
        "      st0 <= 0; st1 <= 0; st2 <= 0; ld0 <= 0; ld1 <= 0; ld2 <= 0;",
        "    end else begin",
        "      lv <= {lv[1:0], data_load_req_o}; sv <= {sv[1:0], data_store_req_o};",
        "      lt0 <= data_load_tag_o; lt1 <= lt0; lt2 <= lt1;",
        "      st0 <= data_store_tag_o; st1 <= st0; st2 <= st1;",
        "      ld0 <= load_value; ld1 <= ld0; ld2 <= ld1;",
        "    end",
        "  end",
        "  // These are proof obligations, never premises on internal service.",
        "  always @* if (rst_ni) begin",
        "    assert (!data_load_rvalid_i || data_load_rready_o);",
        "    assert (!data_store_rvalid_i || data_store_rready_o);",
        f"    assert (!(probe_insert && probe_index < 3'd{threshold}));",
        "  end", "endmodule", ""]
    return "\n".join(lines)


def main():
    workspace = workspace_root(HERE)
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--frontend", type=Path, default=workspace/"experiments/bounded_dynamic/len5/build/pre_fpu_frontend")
    ap.add_argument("--disassembly", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--gap", type=int, default=2)
    ap.add_argument("--threshold", type=int, default=4)
    ap.add_argument("--timeout", type=int, default=120)
    ap.add_argument("--datapath-abstraction", choices=("none", "alu_mul", "alu_mul_branch_taken"), default="none")
    ap.add_argument("--yosys", default=str(workspace/"tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys"))
    ap.add_argument("--abc", default="/usr/local/bin/abc")
    args = ap.parse_args()
    if args.gap < 1 or not 1 <= args.threshold <= 7:
        ap.error("Require gap >= 1 and threshold in 1..7")
    out = args.output.resolve(); out.mkdir(parents=True, exist_ok=False)
    (out/"formal_screen.py").write_bytes(Path(__file__).read_bytes())
    fm = json.loads((args.frontend/"manifest.json").read_text())
    assert fm["upstream_commit"] == PRE_FPU_PIN and fm["original_sha256"] == fm["prepared_sha256"]
    rtlil = args.frontend/"normalized.il"
    assert digest(rtlil) == fm["normalized_il_sha256"]
    for path, expected in fm["prepared_sha256"].items():
        assert digest(args.frontend/"source"/path) == expected
    source = out/"source.json"
    source_export = checked_yosys(args.yosys,
        f"read_rtlil {yosys_path(rtlil)}\ncheck -assert\nwrite_json {yosys_path(source)}\n",
        out, "source_export", args.timeout)
    design = json.loads(source.read_text())
    abstraction = None
    abstraction_source = None
    if args.datapath_abstraction != "none":
        from abstract_datapath import abstract_datapath
        abstraction_source = HERE/"abstract_datapath.py"
        (out/"abstract_datapath.py").write_bytes(abstraction_source.read_bytes())
        design, abstraction = abstract_datapath(design, "datapath", mode=args.datapath_abstraction)
        (out/"abstraction.json").write_text(json.dumps(abstraction, indent=2)+"\n")
    module = design["modules"]["datapath"]
    for alias, original in (("probe_insert", "insert"), ("probe_index", "new_idx")):
        bits = module["netnames"]["u_backend.u_exec_stage.u_alu_unit.u_arith_rs."+original]["bits"]
        module["ports"][alias] = {"direction":"output", "bits":bits}
    instructions = []
    for addr, word in re.findall(r"(?m)^\s*([0-9a-f]+):\s+([0-9a-f]{8})\s", args.disassembly.read_text()):
        if int(addr, 16) < 0x38:
            instructions.append(int(word, 16))
    if len(instructions) != 14:
        raise ValueError("Unexpected streaming kernel text; audit its alphabet")
    core = out/"core.v"
    export_design(design, "datapath", "ObservedCore", core, args.yosys, args.timeout)
    monitor = out/"AdmissionScreen.sv"
    monitor.write_text(harness(module["ports"], instructions, args.gap, args.threshold))
    record = {"status":"running", "accepted_optimization":False,
        "scope":"Original whole-core safety screen over the streaming instruction alphabet; not an exact program trace model",
        "source_commit":PRE_FPU_PIN, "source_json_sha256":digest(source),
        "source_rtlil_sha256":digest(rtlil), "source_export":source_export,
        "datapath_abstraction":abstraction, "abstraction_mode":args.datapath_abstraction,
        "abstraction_helper_sha256":digest(abstraction_source) if abstraction_source else None,
        "core_sha256":digest(core), "core_json_sha256":digest(core.with_suffix(".json")), "harness_sha256":digest(monitor),
        "script_sha256":digest(Path(__file__)), "instruction_alphabet":[f"{x:08x}" for x in instructions],
        "instruction_acceptance_gap":args.gap, "instruction_min_response_latency":2,
        "instruction_pipeline_stages":2, "instruction_pipeline_enable":"core instr_rready_o",
        "flush_semantics":"clear pending instruction stages at edge; retain data replies", "data_response_latency":3,
        "memory_faults":False, "memory_domain":"Nonfaulting mapped RAM, with arbitrary load values independent of addresses",
        "nonfaulting_response_code":31, "invalid_response_codes":[0,31],
        "forbidden_ALU_insertion_indices":list(range(args.threshold))}
    def save(): (out/"summary.json").write_text(json.dumps(record, indent=2)+"\n")
    save()
    try:
        record["prepare"] = checked_yosys(args.yosys,
            f"read_json {yosys_path(core.with_suffix('.json'))}\nrename datapath ObservedCore\n"
            "bwmuxmap\nbmuxmap\ndemuxmap\n"
            f"read_verilog -formal -sv {yosys_path(monitor)}\n"
            "prep -top AdmissionScreen -flatten\ncheck -assert\n"+formal_lower_command(args.yosys)+
            "select -assert-count 3 t:$assert\nselect *\nmemory_map\nopt_clean\nasync2sync\ndffunmap\n"
            f"write_json {yosys_path(out/'screen.json')}\n", out, "prepare", args.timeout)
        model = json.loads((out/"screen.json").read_text())
        record["clock_model"] = validate_single_clock(model, "AdmissionScreen")
        record["export"] = checked_yosys(args.yosys,
            f"read_json {yosys_path(out/'screen.json')}\n"
            "formalff -clk2ff\nsetundef -anyseq\nopt -keepdc\ntechmap\nopt -keepdc\n"
            "setundef -anyseq\naigmap\n"
            f"write_aiger -zinit -symbols {yosys_path(out/'screen.aig')}\n", out, "export", args.timeout)
        aig = out/"screen.aig"
        with aig.open("rb") as f: header = f.readline().decode().split()
        assert header[0] == "aig" and int(header[4]) == 0 and int(header[6]) == 3
        record["aig_header"] = header
        record["aig_sha256"] = digest(aig)
        command = f'read_aiger "{aig}"; fold; orpos; pdr -T {args.timeout} -v'
        record["pdr"] = run_command([args.abc,"-c",command], out/"pdr.log", args.timeout+5)
        log = (out/"pdr.log").read_text()
        if record["pdr"]["returncode"] == 0 and not record["pdr"]["timeout"]:
            if (len(re.findall(r"(?m)^Property proved\.", log)) == 1
                    and not re.search(r"\b(error|failed|undecided|disproved|timed out|time limit|was asserted)\b", log, re.I)):
                record["status"] = "proved_safety_query_only"
            elif "was asserted" in log:
                record["status"] = "counterexample_in_overapproximated_domain"
            else: record["status"] = "unknown"
        else: record["status"] = "unknown"
    except (ValueError, RuntimeError, OSError, AssertionError) as error:
        record.update(status="error", error=str(error))
    for key, path in (("core", core), ("core_json", core.with_suffix(".json")), ("harness", monitor), ("script", Path(__file__))):
        if digest(path) != record[key+"_sha256"]:
            record.update(status="error", error=f"{key} changed during screen")
    if abstraction_source and digest(abstraction_source) != record["abstraction_helper_sha256"]:
        record.update(status="error", error="Abstraction helper changed during screen")
    save(); print(json.dumps({k:record[k] for k in ("status", "accepted_optimization")}))


if __name__ == "__main__":
    main()
