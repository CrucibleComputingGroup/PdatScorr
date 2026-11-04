#!/usr/bin/env python3
"""Source-audited inductive LSQ nonalias proof; NOT a whole-core RTL proof.

The entry transition relation below manually extracts the address/finished
fields from pinned RSD RTL. Every invocation checks exact source hashes.
Z3 discharges reset, one-step induction, and observable-cut implications.
Unrestricted symbolic per-entry allocation/execution permits all pointer,
recovery, stall and replay sequences, including sequences RSD cannot generate.
The address contract applies to every executed speculative operation.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import time
from pathlib import Path

import z3

HERE = Path(__file__).resolve().parent
SOURCE_HASHES = {
    "LoadStoreUnit/LoadQueue.sv": "3a4a33e0aa5586aace17b09da68f466d09fbb9914fd744e49b261f2df927d701",
    "LoadStoreUnit/StoreQueue.sv": "f344b1f219920f59e48eba6bcb809130df060afd47dc6b257bb0c72653167ecf",
    "LoadStoreUnit/LoadStoreUnitTypes.sv": "321f9a0b9f661b8da3566e4158b9aca635eaba2bad94e9c20f83ff20a5162e8a",
    "LoadStoreUnit/LoadStoreUnit.sv": "56cdc0b0e2faa1f87353efa954fc92d64e632a07c61962122be6afac7b38e99d",
    "Memory/MemoryMapTypes.sv": "8d8b7a38a458d1d6a1252005149404affda46a1d993771ca6bf691f7015b2f88",
    "Primitives/Picker.sv": "b04be6166d16060583d98983735c232cfb741dfaa3a50b5d6913392d154b60dc",
    "Pipeline/MemoryBackEnd/MemoryTagAccessStage.sv": "a7e7ccce55fe9a4671c2371693c31ab507ee16323ea25310e824604d9f8ac049",
}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--src", type=Path, default=HERE.parent / "rsd/Processor/Src")
    parser.add_argument("--output", type=Path, default=HERE / "results")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    source_audit = []
    for relative, expected in SOURCE_HASHES.items():
        path = args.src / relative
        observed = hashlib.sha256(path.read_bytes()).hexdigest()
        if observed != expected:
            raise RuntimeError(f"Source audit failed: {path}: {observed} != {expected}")
        source_audit.append({"path": str(path.resolve()), "sha256": observed})

    obligations = []

    def check(name, assumptions, claim, expected=z3.unsat):
        solver = z3.Solver()
        solver.set(timeout=30000)
        solver.add(*assumptions)
        solver.add(z3.Not(claim))
        (args.output / f"{name}.smt2").write_text(solver.to_smt2())
        started = time.monotonic()
        result = solver.check()
        record = {"name": name, "result": str(result), "expected": str(expected),
                  "seconds": time.monotonic() - started}
        if result == z3.sat:
            record["witness"] = str(solver.model())
        obligations.append(record)
        print(f"{name}: {result} (expected {expected})", flush=True)
        if result != expected:
            raise RuntimeError(f"Failed obligation {name}: {result}")

    # The arbitrary selected entry has no constraints on its initial address.
    # reset clears finished, execution writes address, later-in-source allocation
    # overrides finished to false. This captures nonblocking assignment priority.
    rst, alloc_l, alloc_s, exec_l, exec_s, cond_s = z3.Bools(
        "rst alloc_l alloc_s exec_l exec_s cond_s")
    hit_l, hit_s = z3.Bools("execution_targets_l_entry execution_targets_s_entry")
    lf, sf, lreg = z3.Bools("l_finished s_finished l_reg_valid")
    la, sa = z3.BitVecs("l_stored_block_addr s_stored_block_addr", 20)
    load, store = z3.BitVecs("executed_load_phy_addr executed_store_phy_addr", 22)
    load_block, store_block = z3.Extract(21, 2, load), z3.Extract(21, 2, store)
    low = lambda address: z3.Extract(19, 14, address) == 0
    inv_l = z3.Implies(lf, low(la))
    inv_s = z3.Implies(sf, z3.Not(low(sa)))
    contract = [z3.Implies(z3.And(z3.Not(rst), exec_l), z3.Extract(21, 16, load) == 0),
                z3.Implies(z3.And(z3.Not(rst), exec_s), z3.Extract(21, 16, store) != 0)]

    next_lf = z3.If(rst, False, z3.If(alloc_l, False,
                 z3.If(z3.And(exec_l, hit_l), True, lf)))
    next_la = z3.If(z3.And(z3.Not(rst), exec_l, hit_l), load_block, la)
    next_sf = z3.If(rst, False, z3.If(alloc_s, False,
                 z3.If(z3.And(exec_s, hit_s), cond_s, sf)))
    next_sa = z3.If(rst, z3.BitVecVal(0, 20),
                 z3.If(z3.And(exec_s, hit_s), store_block, sa))
    next_inv_l = z3.Implies(next_lf, low(next_la))
    next_inv_s = z3.Implies(next_sf, z3.Not(low(next_sa)))
    check("lq_reset_base", [rst], next_inv_l)
    check("sq_reset_base", [rst], next_inv_s)
    check("lq_inductive_step", [inv_l, *contract], next_inv_l)
    check("sq_inductive_step", [inv_s, *contract], next_inv_s)

    # Word/byte overlap, legal-memory and age predicates remain unconstrained:
    # disjoint block addresses suffice regardless of these additional gates.
    word_overlap, byte_overlap, legal, age_in_range = z3.Bools(
        "word_overlap byte_overlap legal_memory age_in_range")
    lmatch = z3.And(lf, lreg, la == store_block, word_overlap)
    smatch = z3.And(sf, legal, sa == load_block, word_overlap, byte_overlap)
    check("lq_stored_match_zero_for_executed_store",
          [z3.Not(rst), inv_l, exec_s, *contract], z3.Not(lmatch))
    check("sq_stored_match_zero_for_executed_load",
          [z3.Not(rst), inv_s, exec_l, *contract], z3.Not(smatch))
    check("same_cycle_match_zero_when_both_execute",
          [z3.Not(rst), exec_l, exec_s, *contract], load_block != store_block)
    # LQ's combinational same-cycle loop lacks an executeStore guard. We do NOT
    # cut that loop. With the stored-match vector zero, its result remains exact.
    same_cycle_conflict, same_cycle_pc = z3.Bool("same_cycle_conflict"), z3.BitVec("same_cycle_pc", 19)
    historical = z3.And(exec_s, age_in_range, lmatch)
    original_conflict = z3.Or(historical, same_cycle_conflict)
    original_pc = z3.If(same_cycle_conflict, same_cycle_pc,
                         z3.If(historical, z3.BitVec("historical_pc", 19), 0))
    candidate_pc = z3.If(same_cycle_conflict, same_cycle_pc, 0)
    check("lq_historical_cut_observable_equality",
          [z3.Not(rst), inv_l, *contract],
          z3.And(original_conflict == same_cycle_conflict, original_pc == candidate_pc))

    # For SQ the enable is zero every cycle: active load => disjoint addresses;
    # inactive load => explicit executeLoad gate. Data/miss outputs are ODCs.
    forwarded = z3.And(exec_l, age_in_range, smatch)
    check("sq_forwarding_enable_zero", [z3.Not(rst), inv_s, *contract], z3.Not(forwarded))
    miss = z3.Bool("arbitrary_forward_miss")
    check("sq_miss_consumer_mask", [z3.Not(forwarded)], z3.Not(z3.And(forwarded, miss)))
    saved_forward, stall = z3.Bools("saved_forward backend_stall")
    next_forward = z3.If(rst, False, z3.If(stall, saved_forward, forwarded))
    check("lsu_forward_flag_reset_base", [rst], z3.Not(next_forward))
    check("lsu_forward_flag_inductive_step", [z3.Not(saved_forward), z3.Not(forwarded)], z3.Not(next_forward))
    arbitrary_data, retained_data = z3.BitVecs("arbitrary_forward_data retained_cache_or_mshr_data", 32)
    check("lsu_forward_data_consumer_mask", [z3.Not(saved_forward)],
          z3.If(saved_forward, arbitrary_data, retained_data) == retained_data)

    # Negative controls prevent a vacuous/tautological comparator model.
    # Removing the store-side contract permits a real historical LQ match.
    check("negative_without_store_contract", [z3.Not(rst), inv_l, exec_s, lf, lreg,
          word_overlap, low(la), store_block == la], z3.Not(lmatch), z3.sat)
    check("negative_without_load_contract", [z3.Not(rst), inv_s, exec_l, sf, legal,
          word_overlap, byte_overlap, load_block == sa], z3.Not(smatch), z3.sat)
    # Simultaneous enabled load/store, allocation and eventual matches are not
    # prohibited by resetting or requiring execute=0. This is a SAT witness.
    check("contract_nonvacuity", [z3.Not(rst), exec_l, exec_s, alloc_l, alloc_s,
          load == 0x1000, store == 0x10000, *contract], z3.BoolVal(False), z3.sat)

    # A validity-qualified region invariant is INSUFFICIENT for StoreQueue:
    # its address matcher does not test stored regValid. An invalid speculative
    # store at a transient low address matches a valid low-region load and makes
    # forwardMiss true. The consumer can release its MSHR/refetch, changing time.
    sreg = z3.Bool("stored_store_reg_valid")
    weak_store_invariant = z3.Implies(z3.And(sf, sreg), z3.Not(low(sa)))
    check("negative_valid_store_only_contract", [weak_store_invariant,
          z3.Not(sreg), sf, exec_l, legal, word_overlap, byte_overlap,
          load == 0x1000, sa == 0x400], z3.Not(smatch), z3.sat)

    # Symmetrically, executeLoad is not gated by register validity. Even a
    # transient invalid load may trigger forwarding-related MSHR bookkeeping.
    load_operand_valid = z3.Bool("load_operand_valid")
    weak_load_contract = z3.Implies(z3.And(exec_l, load_operand_valid),
                                   z3.Extract(21, 16, load) == 0)
    check("negative_valid_load_only_contract", [inv_s, weak_load_contract,
          z3.Not(load_operand_valid), exec_l, sf, legal, word_overlap,
          byte_overlap, load == 0x10000, sa == 0x4000], z3.Not(smatch), z3.sat)

    # RSD reserves one sentinel and RENAME_WIDTH slots at pre-admission. A
    # capacity that exceeds the next occupancy may still introduce a stall.
    occupancy, allocations, releases = z3.Ints("occupancy allocations releases")
    baseline_admits = occupancy <= 16 - 2 - 1
    reduced_admits = occupancy <= 8 - 2 - 1
    check("negative_peak_occupancy_sizing", [occupancy == 6, allocations == 1,
          releases == 0, occupancy + allocations - releases < 8,
          baseline_admits], reduced_admits, z3.sat)

    # Prove the actual RSD circular-picker cone returns no
    # picked request for zero comparator bits, for arbitrary head/tail pointers.
    picker = (args.src / "Primitives/Picker.sv").read_text()
    picker = picker[picker.index("module CircularRangePicker #("):]
    # Yosys 0.33 does not propagate direction across typed ANSI declarations.
    # Repeat only the inherited directions; the module body is unchanged.
    picker = picker.replace("    logic [$clog2(ENTRY_NUM)-1:0] tailPtr,",
                            "    input logic [$clog2(ENTRY_NUM)-1:0] tailPtr,")
    picker = picker.replace("    logic [ENTRY_NUM-1:0] request,",
                            "    input logic [ENTRY_NUM-1:0] request,")
    picker = picker.replace("    logic picked\n", "    output logic picked\n")
    picker_path = args.output / "actual_circular_picker.sv"
    picker_path.write_text(picker + """
module picker_contract(input [3:0] head, tail);
  wire [3:0] grant;
  wire picked;
  CircularRangePicker #(.ENTRY_NUM(16)) dut(head, tail, 16'b0, grant, picked);
  always @* assert(!picked);
endmodule
""")
    command = ["yosys", "-p", f"read_verilog -formal -sv {picker_path}; prep -top picker_contract -flatten; sat -verify -prove-asserts -show-inputs"]
    completed = subprocess.run(command, capture_output=True, text=True, timeout=60)
    log = completed.stdout + completed.stderr
    (args.output / "actual_picker_proof.log").write_text(log)
    if completed.returncode or "SAT proof finished - no model found: SUCCESS!" not in log:
        raise RuntimeError("Actual RTL picker proof failed; inspect actual_picker_proof.log")
    obligations.append({"name": "actual_rtl_picker_zero_requests", "result": "proved", "command": command})

    report = {
        "status": "passed", "scope": "Source-audited manual entry-transition extraction with unbounded inductive invariants, plus actual RTL picker combinational proof. NOT full-core equivalence and NOT a proof that any binary satisfies the environment contract.",
        "contract": "After reset, every executeLoad implies 22-bit physical address[21:16]==0; every executeStore implies address[21:16]!=0, including invalid-operand/speculative/replayed/wrong-path operations.",
        "cut": "Only stored-address addrMatch expressions in LoadQueue and StoreQueue are tied to zero. Preserve the entire LQ same-cycle violation loop and SQ commit path.",
        "observation_relation": "LQ conflict and conflictLoadPC exact after reset; SQ storeLoadForwarded exact; forwardMiss/data may differ only while forwarding disabled; LSU latched forwarding enable remains zero and masks data.",
        "source_audit": source_audit, "z3_version": z3.get_version_string(),
        "picker_translation": "Extract CircularRangePicker and its two shifter modules verbatim, then repeat inherited ANSI input/output port directions for Yosys 0.33 compatibility; no body changes.",
        "obligations": obligations,
        "limitations": ["Manual transition extraction is source-reviewed, not a mechanically verified translation of complete LSQ RTL.", "Arbitrary per-entry hit/allocation predicates overapproximate recovery and pointer sequences; queue capacity and ordering logic are unmodified.", "Proof begins with reset; pre-reset arbitrary internal values are outside its scope.", "Application/environment adherence requires separate checking; successful example simulations are not an all-input proof."]
    }
    (args.output / "proof_summary.json").write_text(json.dumps(report, indent=2) + "\n")
    print("PASS: inductive entry invariants, observable-cut obligations, negative controls, and actual RTL picker proof")


if __name__ == "__main__":
    main()
