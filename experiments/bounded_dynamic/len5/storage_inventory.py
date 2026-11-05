#!/usr/bin/env python3
"""Count actual sequential Q bits in qualified LEN5 netlists; no optimization run.

Inputs are the previously exported normalized model and ordinary Yosys opt result.
Counts are structural storage proxies, never library area or optimization savings.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from prepare_frontend import PRE_FPU_PIN, digest, workspace_root

FF_TYPES = {"$aldff", "$aldffe", "$adff", "$adffe", "$dff", "$dffe",
            "$sdff", "$sdffe", "$sdffce", "$ff"}
BANKS = (
    ("ROB payload", "u_backend.u_commit_stage.u_rob.data", 32, "rotating ROB tail"),
    ("Store-buffer payload", "u_backend.u_exec_stage.u_load_store_unit.u_store_buffer.data", 16, "rotating tail; CACHED data retained for forwarding"),
    ("Integer register file", "u_backend.u_int_rf.rf_data", 31, "architectural register indexed; x0 absent"),
    ("Branch target buffer", "u_fetch_stage.u_bpu.u_btb.btb_q", 16, "PC indexed"),
    ("ALU RS payload", "u_backend.u_exec_stage.u_alu_unit.u_arith_rs.data", 8, "highest-index free first"),
    ("Load-buffer payload", "u_backend.u_exec_stage.u_load_store_unit.u_load_buffer.data", 8, "rotating tail"),
    ("Branch RS payload", "u_backend.u_exec_stage.u_branch_unit.u_branch_rs.data", 4, "rotating tail"),
    ("Multiply RS payload", "u_backend.u_exec_stage.gen_mult_unit.u_mult_unit.gen_parallel_mult_unit.u_mult_rs.data", 4, "highest-index free first"),
    ("Divide RS payload", "u_backend.u_exec_stage.gen_div_unit.u_div_unit.u_div_rs.data", 4, "highest-index free first"),
    ("Predispatch issue FIFO", "u_backend.u_issue_stage.u_issue_fifo.data", 4, "rotating FIFO"),
    ("Return-address stack", "u_fetch_stage.u_early_jump_unit.u_ras.ras_addr", 8, "stack index"),
    ("Fetch prediction FIFO", "u_fetch_stage.u_mem_if.u_pred_fifo.gen_fifo.data", 2, "rotating FIFO"),
)


def count(path: Path) -> dict:
    module = json.loads(path.read_text())["modules"]["datapath"]
    qbits = set()
    ff_cells = 0
    for cell in module["cells"].values():
        if cell["type"] in FF_TYPES:
            ff_cells += 1
            qbits.update(b for b in cell["connections"]["Q"] if isinstance(b, int))
    result = {"input_sha256": digest(path.read_bytes()), "unique_ff_bits": len(qbits),
              "word_level_ff_cells": ff_cells, "word_level_cells": len(module["cells"]), "banks": []}
    counted = set()
    for label, name, entries, allocator in BANKS:
        bits = module["netnames"][name]["bits"]
        bank = set(bits) & qbits
        assert not counted & bank, f"Overlapping named storage banks: {name}"
        counted |= bank
        assert len(bits) % entries == 0
        width = len(bits) // entries
        per_entry = [len(set(bits[i*width:(i+1)*width]) & qbits) for i in range(entries)]
        result["banks"].append(dict(name=label, net=name, entries=entries, allocator=allocator,
                                    declared_bits=len(bits), unique_ff_bits=len(bank),
                                    per_entry_ff_bits=per_entry,
                                    percent_core_ff_bits=100*len(bank)/len(qbits)))
    result["other_ff_bits"] = len(qbits - counted)
    rs = [b for b in result["banks"] if b["name"] in ("ALU RS payload", "Multiply RS payload", "Divide RS payload")]
    result["all_first_free_payload_ff_bits"] = sum(b["unique_ff_bits"] for b in rs)
    result["all_first_free_payload_percent_core_ff_bits"] = 100*result["all_first_free_payload_ff_bits"]/len(qbits)
    return result


def main() -> None:
    here = Path(__file__).resolve().parent
    outer = workspace_root(here)/"experiments/bounded_dynamic/len5/build"
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--inventory-dir", type=Path, default=outer/"storage_inventory")
    ap.add_argument("--frontend", type=Path, default=outer/"pre_fpu_frontend")
    ap.add_argument("--output", type=Path, default=here/"results/storage_inventory.json")
    args = ap.parse_args()
    manifest = json.loads((args.frontend/"manifest.json").read_text())
    assert manifest["upstream_commit"] == PRE_FPU_PIN
    assert manifest["original_sha256"] == manifest["prepared_sha256"]
    assert digest((args.frontend/"normalized.il").read_bytes()) == manifest["normalized_il_sha256"]
    results = {"scope": "Read-only structural inventory plus ordinary word-level opt; no mapping, timing optimization, proof, or claimed savings",
               "upstream_commit": PRE_FPU_PIN,
               "frontend_manifest_sha256": digest((args.frontend/"manifest.json").read_bytes()),
               "input_rtlil_sha256": manifest["normalized_il_sha256"],
               "inventory_script_sha256": digest(Path(__file__).read_bytes()),
               "normalized": count(args.inventory_dir/"normalized.json"),
               "ordinary_opt": count(args.inventory_dir/"ordinary_opt.json"),
               "ordinary_opt_commands": "read_rtlil qualified normalized.il; opt; stat; write_json ordinary_opt.json",
               "ordinary_opt_log_sha256": digest((args.inventory_dir/"ordinary_opt.log").read_bytes()),
               "limits": ["FF-bit counts are not physical area and exclude combinational mux/multiplier cost.",
                          "ISA-restricted comparisons require the same ISA-only optimized baseline; this inventory uses full pre-FPU integer defaults.",
                          "First-free polarity is highest index first; low indices are the possible unreachable entries.",
                          "Unreachable valid state does not by itself prove payload zero or raw-output equivalence during flush."]}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2)+"\n")
    print(json.dumps({k:results["ordinary_opt"][k] for k in ("unique_ff_bits","all_first_free_payload_ff_bits","all_first_free_payload_percent_core_ff_bits")}))


if __name__ == "__main__":
    main()
