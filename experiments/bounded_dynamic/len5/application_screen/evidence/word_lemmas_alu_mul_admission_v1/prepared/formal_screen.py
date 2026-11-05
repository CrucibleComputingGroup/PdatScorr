#!/usr/bin/env python3
"""Screen an RS admission bound on original LEN5 under external service rules.

With --program-hex, instruction replies use an address-indexed immutable ROM;
otherwise they choose a word from the broader streaming instruction alphabet.
The query does NOT assume a PC sequence, operand readiness, occupancy, or issue
rate. Data memory supplies arbitrary load values. Alphabet counterexamples need
not be legal traces of the actual program. --zero-fault-data selects the explicit
Harvard platform's zero instruction payload on misaligned/unmapped fetches.
This is a safety query, not an optimizer or an accepted replacement design.
"""
from __future__ import annotations
import argparse
import copy
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
sys.path.insert(0, str(REPO))
sys.path.insert(0, str(HERE.parent))
from odc.temporal import checked_yosys, digest, export_design, formal_lower_command, formal_prepare_command, run_command, validate_single_clock, yosys_path
from prepare_frontend import PRE_FPU_PIN, workspace_root


def add_native_probes(design):
    """Expose existing native signals without changing drivers or cell inventory."""
    result = copy.deepcopy(design)
    module = result['modules']['datapath']
    for alias, original in (("probe_insert", "insert"), ("probe_index", "new_idx")):
        if alias in module['ports']:
            raise ValueError('Native probe port already exists: '+alias)
        bits = module['netnames']['u_backend.u_exec_stage.u_alu_unit.u_arith_rs.'+original]['bits']
        module['ports'][alias] = {'direction': 'output', 'bits': list(bits)}
    return result


def validate_query_only_delta(native, query, imported_cells):
    """A theorem query may add only its certified predicates and assumptions."""
    extra = set(imported_cells)
    stripped = copy.deepcopy(query)
    module = stripped['modules']['datapath']
    for name in extra:
        if name not in module['cells'] or module['cells'][name]['type'] not in ('$eq', '$reduce_or', '$assume'):
            raise ValueError('Unexpected theorem cell: '+name)
        del module['cells'][name]
    if stripped != native:
        raise ValueError('Proof-only model changed native hardware or its observation ports')
    counts = {kind: sum(c['type'] == '$'+kind for c in query['modules']['datapath']['cells'].values())
              for kind in ('assert', 'assume', 'cover')}
    if counts != {'assert': 0, 'assume': 7, 'cover': 0}:
        raise ValueError('Proof-only model must contain exactly seven derived assumptions')
    return counts


def abstract_query_model(design, mode, word_import=None):
    """Apply reviewed payload overapproximation only after theorem imports."""
    from abstract_datapath import abstract_datapath
    result, audit = abstract_datapath(design, 'datapath', mode=mode)
    if word_import:
        if mode != 'alu_mul':
            raise ValueError('Only the reviewed ALU/multiplier composition is supported with word lemmas')
        protected = set(word_import['source_projection_data_cells']) | set(word_import['source_projection_preserved_control_cells'])
        protected |= set(word_import['added_cells'])
        if set(audit['native_cells_removed']) & protected:
            raise ValueError('Proof abstraction intersects certified native word logic')
        before, after = design['modules']['datapath']['cells'], result['modules']['datapath']['cells']
        if any(before[name] != after.get(name) for name in protected):
            raise ValueError('Proof abstraction changed certified word-theorem logic')
        audit['all_certified_word_projection_and_assumption_cells_unchanged'] = True
        audit['certified_word_projection_cells'] = sorted(protected-set(word_import['added_cells']))
        audit['certified_lemma_encoding_cells'] = list(word_import['added_cells'])
    return result, audit


def harness(ports, instructions, gap, threshold, rom=None, zero_fault_data=False):
    lines = ["module AdmissionScreen(input wire clk_i, rst_ni,",
             "  input wire [3:0] instruction_choice, input wire [63:0] load_value,",
             "  input wire [2:0] invalid_code_nonzero, input wire [31:0] instruction_fault_data);",
             "  always @* if ($initstate) assume (!rst_ni);"]
    widths = {n:len(p["bits"]) for n,p in ports.items()}
    for name, width in widths.items():
        if name not in ("clk_i", "rst_ni"):
            lines.append(f"  wire [{width-1}:0] {name};")
    lines += ["  ObservedCore dut(" + ",".join(f".{n}({n})" for n in ports) + ");",
              "  reg [31:0] selected_instruction;",
              "  reg selected_instruction_fault; reg [4:0] selected_instruction_code;"]
    if rom is not None:
        from program_rom import verilog_selector
        lines += verilog_selector(rom, zero_fault_data=zero_fault_data)
    else:
        lines += ["  always @* begin", "    selected_instruction = 32'h00000013;",
                  "    selected_instruction_fault = 0; selected_instruction_code = 31;",
                  "    case (instruction_choice)"]
        if len(instructions) > 16:
            raise ValueError("The v1 alphabet selector supports at most 16 instructions")
        for index, word in enumerate(instructions):
            lines.append(f"      4'd{index}: selected_instruction = 32'h{word:08x};")
        lines += ["      default: ;", "    endcase", "  end"]
    lines += [
        "  assign irq_i = 0;", "  assign fetch_enable_i = 1;",
        "  assign instr_except_raised_i = ifault[1];",
        "  assign instr_except_code_i = icode1;",
        "  assign data_load_except_raised_i = 0;",
        "  assign data_load_except_code_i = (data_load_rvalid_i || invalid_code_nonzero[1]) ? 31 : 0;",
        "  assign data_store_except_raised_i = 0;",
        "  assign data_store_except_code_i = (data_store_rvalid_i || invalid_code_nonzero[2]) ? 31 : 0;",
        "  // Native two-stage fetch pipeline: freeze with core response readiness.",
        "  // SKIP_INS_ANS_REG=1 couples upstream grant to this same readiness.",
        "  reg [1:0] iv, ifault; reg [31:0] ins0, ins1; reg [4:0] icode0, icode1;",
        f"  reg [{max(1,(gap-1).bit_length())-1}:0] gap_left;",
        "  wire gate_open = gap_left == 0;",
        "  wire ipush = instr_req_o && instr_gnt_i;",
        "  assign instr_gnt_i = instr_rready_o && gate_open;",
        "  assign instr_rvalid_i = iv[1];",
        "  assign instr_rdata_i = ins1;",
        "  always @(posedge clk_i) begin",
        "    if (!rst_ni) begin",
        "      iv <= 0; ifault <= 0; ins0 <= 0; ins1 <= 0; icode0 <= 0; icode1 <= 0; gap_left <= 0;",
        "    end else begin",
        "      if (gap_left != 0) gap_left <= gap_left - 1;",
        f"      if (ipush) gap_left <= {gap-1};",
        "      if (mem_flush_o) begin iv <= 0; ifault <= 0; ins0 <= 0; ins1 <= 0; icode0 <= 0; icode1 <= 0; end",
        "      else if (instr_rready_o) begin",
        "        iv <= {iv[0], instr_req_o && gate_open};",
        "        ins0 <= (instr_req_o && gate_open) ? selected_instruction : 0;",
        "        ins1 <= ins0;",
        "        ifault <= {ifault[0], instr_req_o && gate_open && selected_instruction_fault};",
        "        icode0 <= (instr_req_o && gate_open) ? selected_instruction_code : 31;",
        "        icode1 <= icode0;",
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
    ap.add_argument("--program-hex", type=Path, help="Immutable instruction ROM image; omit for the broader alphabet domain")
    ap.add_argument("--zero-fault-data", action="store_true", help="Use the declared Harvard platform's zero payload on instruction faults")
    ap.add_argument("--decoder-certificate", type=Path, help="Replay an exact-alphabet decoder certificate before substituting its native candidate")
    ap.add_argument("--word-domain-lemmas", action="store_true", help="Import seven source-bound native word theorems into a separate proof-only model")
    ap.add_argument("--rom-domain-proof", type=Path, help="Exact external ROM producer theorem required for --word-domain-lemmas")
    ap.add_argument("--engine", choices=("pdr", "bmc", "prepare"), default="pdr")
    ap.add_argument("--frames", type=int, default=48, help="Bounded falsifier depth; never an unbounded certificate")
    ap.add_argument("--gap", type=int, default=2)
    ap.add_argument("--threshold", type=int, default=4)
    ap.add_argument("--timeout", type=int, default=120)
    ap.add_argument("--datapath-abstraction", choices=("none", "alu_mul", "alu_mul_branch_taken"), default="none")
    ap.add_argument("--yosys", default=str(workspace/"tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys"))
    ap.add_argument("--abc", default="/usr/local/bin/abc")
    args = ap.parse_args()
    if args.gap < 1 or not 1 <= args.threshold <= 7:
        ap.error("Require gap >= 1 and threshold in 1..7")
    if args.zero_fault_data and not args.program_hex:
        ap.error("--zero-fault-data requires --program-hex")
    if args.decoder_certificate and (not args.program_hex or not args.zero_fault_data or
            (args.datapath_abstraction != 'none' and not (args.word_domain_lemmas and args.datapath_abstraction == 'alu_mul'))):
        ap.error("--decoder-certificate requires an exact zero-fault ROM; abstraction is allowed only as reviewed alu_mul after --word-domain-lemmas")
    if bool(args.word_domain_lemmas) != bool(args.rom_domain_proof) or (args.word_domain_lemmas and not args.decoder_certificate):
        ap.error("--word-domain-lemmas and --rom-domain-proof require each other and --decoder-certificate")
    out = args.output.resolve(); out.mkdir(parents=True, exist_ok=False)
    (out/"formal_screen.py").write_bytes(Path(__file__).read_bytes())
    temporal_helper = REPO/"odc/temporal.py"
    (out/"temporal.py").write_bytes(temporal_helper.read_bytes())
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
    rom = None
    rom_helper = None
    if args.program_hex:
        from program_rom import read_image
        rom = read_image(args.program_hex)
        rom_helper = HERE/"program_rom.py"
        (out/"program_rom.py").write_bytes(rom_helper.read_bytes())
        (out/"program.hex").write_bytes(args.program_hex.read_bytes())
        (out/"rom.json").write_text(json.dumps(rom, indent=2)+"\n")
    decoder_import = None
    decoder_helper = None
    if args.decoder_certificate:
        from certified_decoder import import_decoder
        decoder_helper = HERE/"certified_decoder.py"
        design, decoder_import = import_decoder(args.decoder_certificate, source, rom,
            out/"certified_decoder", certifier=HERE.parent/"isa_baseline/certify.py",
            zero_fault_data=args.zero_fault_data, initial_reset=True, timeout=args.timeout)
    abstraction = None
    abstraction_source = None
    unobserved_native = design
    design = add_native_probes(design)
    module = design["modules"]["datapath"]
    instructions = []
    for addr, word in re.findall(r"(?m)^\s*([0-9a-f]+):\s+([0-9a-f]{8})\s", args.disassembly.read_text()):
        if int(addr, 16) < 0x38:
            instructions.append(int(word, 16))
    if len(instructions) != 14:
        raise ValueError("Unexpected streaming kernel text; audit its alphabet")
    core = out/"core.v"
    export_design(design, "datapath", "ObservedCore", core, args.yosys, args.timeout)
    monitor = out/"AdmissionScreen.sv"
    monitor.write_text(harness(module["ports"], instructions, args.gap, args.threshold, rom, args.zero_fault_data))
    query_core = core.with_suffix('.json')
    query_design = design
    word_import = None
    rom_domain_import = None
    query_native_counts = None
    if args.word_domain_lemmas:
        from certified_decoder import exact_alphabet
        from domain_lemmas import import_word_domain_lemmas
        from rom_domain_import import validate_rom_domain
        alphabet = exact_alphabet(json.loads(args.decoder_certificate.read_text())['domain_expression'])
        rom_domain_import = validate_rom_domain(args.rom_domain_proof, monitor, core.with_suffix('.json'), rom,
            out/'external_rom_theorem', allowed_words=alphabet, yosys=args.yosys, timeout=args.timeout)
        lemma_design, word_import = import_word_domain_lemmas(args.decoder_certificate, source, unobserved_native, rom,
            out/'native_word_theorems', certifier=HERE.parent/'isa_baseline/certify.py', yosys=args.yosys,
            zero_fault_data=args.zero_fault_data, initial_reset=True, timeout=args.timeout)
        lemma_design = add_native_probes(lemma_design)
        query_native_counts = validate_query_only_delta(design, lemma_design, word_import['added_cells'])
        query_design = lemma_design
        query_core = out/'lemma_core.json'
        query_core.write_text(json.dumps(lemma_design, indent=2)+'\n')
    if args.datapath_abstraction != 'none':
        abstraction_source = HERE/'abstract_datapath.py'
        (out/'abstract_datapath.py').write_bytes(abstraction_source.read_bytes())
        query_design, abstraction = abstract_query_model(query_design, args.datapath_abstraction, word_import)
        (out/'abstraction.json').write_text(json.dumps(abstraction, indent=2)+'\n')
        query_core = out/'abstract_query_core.json'
        query_core.write_text(json.dumps(query_design, indent=2)+'\n')
    record = {"status":"running", "accepted_optimization":False,
        "scope":("Original whole-core safety query with immutable instruction ROM and overapproximated nonfaulting data service" if rom else
                 "Original whole-core safety screen over the streaming instruction alphabet; not an exact program trace model"),
        "instruction_model":"immutable_rom" if rom else "alphabet",
        "rom_image_sha256":rom["image_sha256"] if rom else None,
        "rom_helper_sha256":digest(rom_helper) if rom_helper else None,
        "instruction_fault_payload":"zero" if args.zero_fault_data else "arbitrary",
        "engine":args.engine, "requested_frames":args.frames if args.engine == "bmc" else None,
        "source_commit":PRE_FPU_PIN, "source_json_sha256":digest(source),
        "certified_decoder_import":decoder_import,
        "external_rom_domain_import":rom_domain_import, "native_word_domain_import":word_import,
        "query_core_path":str(query_core), "query_core_sha256":digest(query_core),
        "proof_only_native_property_counts":query_native_counts,
        "native_hardware_contains_formal_properties":False,
        "source_rtlil_sha256":digest(rtlil), "source_export":source_export,
        "datapath_abstraction":abstraction, "abstraction_mode":args.datapath_abstraction,
        "abstraction_helper_sha256":digest(abstraction_source) if abstraction_source else None,
        "core_sha256":digest(core), "core_json_sha256":digest(core.with_suffix(".json")), "harness_sha256":digest(monitor),
        "script_sha256":digest(Path(__file__)), "instruction_alphabet":[f"{x:08x}" for x in instructions],
        "temporal_helper_sha256":digest(temporal_helper),
        "undefined_value_model":"Symbolic choices before process optimization and after lowering; no initial-state concretization",
        "instruction_acceptance_gap":args.gap, "instruction_min_response_latency":2,
        "instruction_pipeline_stages":2, "instruction_pipeline_enable":"core instr_rready_o",
        "flush_semantics":"clear pending instruction stages at edge; retain data replies", "data_response_latency":3,
        "memory_faults":{"instruction":"address alignment/mapping faults" if rom else False, "data":False},
        "memory_domain":"Immutable instruction image, separate nonfaulting data service with arbitrary load values" if rom else
                        "Nonfaulting mapped RAM, with arbitrary load values independent of addresses",
        "nonfaulting_response_code":31, "invalid_response_codes":[0,31],
        "forbidden_ALU_insertion_indices":list(range(args.threshold))}
    def save(): (out/"summary.json").write_text(json.dumps(record, indent=2)+"\n")
    if decoder_import:
        record["scope"] = "Whole-core safety query with certified exact-alphabet decoder substitution, immutable instruction ROM, and overapproximated nonfaulting data service"
    if word_import:
        record['scope'] += '; seven previously proved instruction-word domains imported only into the proof model after exact external ROM theorem validation'
    if abstraction:
        record['scope'] += '; proof-only payload overapproximation, original native hardware export retained separately'
    save()
    try:
        record["prepare"] = checked_yosys(args.yosys,
            f"read_json {yosys_path(query_core)}\nrename datapath ObservedCore\n"
            "bwmuxmap\nbmuxmap\ndemuxmap\n"
            f"read_verilog -formal -sv {yosys_path(monitor)}\n"
            + formal_prepare_command("AdmissionScreen") + formal_lower_command(args.yosys)+
            f"select -assert-count 3 t:$assert\nselect -assert-count {8 if word_import else 1} t:$assume\nselect *\nmemory_map\nsetundef -anyseq\nopt_clean\nasync2sync\ndffunmap\nsetundef -anyseq\n"
            f"write_json {yosys_path(out/'screen.json')}\n", out, "prepare", args.timeout)
        model = json.loads((out/"screen.json").read_text())
        record['query_property_counts'] = {kind:sum(c['type'] == '$'+kind for c in model['modules']['AdmissionScreen']['cells'].values())
                                           for kind in ('assert', 'assume', 'cover')}
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
        if args.engine == "prepare":
            record["status"] = "prepared_query_only"
        else:
            action = f"pdr -T {args.timeout} -v" if args.engine == "pdr" else f"bmc3 -F {args.frames} -T {args.timeout} -v"
            command = (f'read_aiger "{aig}"; fold; orpos; {action}; '
                       f'write_cex -a "{out / "counterexample.aiw"}"')
            execution = run_command([args.abc,"-c",command], out/(args.engine+".log"), args.timeout+5)
            record[args.engine] = execution
            log = (out/(args.engine+".log")).read_text()
            record["status"] = "unknown"
            if execution["returncode"] == 0 and not execution["timeout"]:
                if (args.engine == "pdr" and len(re.findall(r"(?m)^Property proved\.", log)) == 1
                        and not re.search(r"\b(error|failed|undecided|disproved|timed out|time limit|was asserted)\b", log, re.I)):
                    record["status"] = "proved_safety_query_only"
                elif "was asserted" in log:
                    record["status"] = "counterexample_in_query_model"
                elif args.engine == "bmc":
                    frames = re.search(r"No output asserted in (\d+) frames\.", log)
                    record["reported_no_counterexample_frames"] = int(frames[1]) if frames else None
                    record["requested_horizon_completed"] = bool(frames and int(frames[1]) >= args.frames and
                        not re.search(r"resource limit|timeout|undecided", log, re.I))
                    record["status"] = ("bounded_only_no_certificate" if record["requested_horizon_completed"]
                                        else "resource_limited_no_certificate")
            witness = out/"counterexample.aiw"
            record["counterexample_sha256"] = digest(witness) if witness.exists() else None
    except (ValueError, RuntimeError, OSError, AssertionError) as error:
        record.update(status="error", error=str(error))
    for key, path in (("source_json", source), ("core", core), ("core_json", core.with_suffix(".json")), ("harness", monitor), ("script", Path(__file__))):
        if digest(path) != record[key+"_sha256"]:
            record.update(status="error", error=f"{key} changed during screen")
    if abstraction_source and digest(abstraction_source) != record["abstraction_helper_sha256"]:
        record.update(status="error", error="Abstraction helper changed during screen")
    if rom_helper and digest(rom_helper) != record["rom_helper_sha256"]:
        record.update(status="error", error="ROM helper changed during screen")
    if digest(temporal_helper) != record["temporal_helper_sha256"]:
        record.update(status="error", error="Temporal helper changed during screen")
    if digest(query_core) != record['query_core_sha256']:
        record.update(status='error', error='Query-only native model changed during screen')
    if args.program_hex and digest(args.program_hex) != record["rom_image_sha256"]:
        record.update(status="error", error="Program image changed during screen")
    if decoder_import:
        for path, expected in ((decoder_helper,decoder_import["importer_sha256"]),
            (args.decoder_certificate,decoder_import["certificate_sha256"]),
            (Path(decoder_import["certifier_path"]),decoder_import["certifier_sha256"]),
            (out/"certified_decoder/native_candidate.json",decoder_import["candidate_native_sha256"])):
            if digest(path) != expected:
                record.update(status="error", error="Certified decoder input or verifier changed during screen")
    if word_import:
        try:
            from domain_lemmas import verify_dependencies as verify_word_dependencies
            from rom_domain_import import verify_dependencies as verify_rom_dependencies
            verify_word_dependencies(word_import)
            verify_rom_dependencies(rom_domain_import)
        except (ValueError, OSError) as error:
            record.update(status='error', error=str(error))
    save(); print(json.dumps({k:record[k] for k in ("status", "accepted_optimization")}))


if __name__ == "__main__":
    main()
