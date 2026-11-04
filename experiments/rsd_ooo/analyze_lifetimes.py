#!/usr/bin/env python3
"""Audit observed MSHR lifetimes, backing read latency and speculative ISA domain.

These are finite trace measurements, never all-input bounds. MSHR lifetime ends
only on the slot's valid falling edge, not on a memory response. Open intervals
at the trace boundaries are reported separately and excluded from complete maxima.
"""
import argparse
import collections
import csv
import hashlib
import json
from pathlib import Path
import statistics

def stats(values):
    values = sorted(values)
    return {"count": len(values), "min": min(values) if values else None,
            "max": max(values) if values else None,
            "mean": statistics.mean(values) if values else None,
            "p95": values[max(0, (95*len(values)+99)//100-1)] if values else None}

def analyze(directory):
    active, previous, closed, censored, errors = {}, {}, [], [], []
    slot_samples = collections.Counter()
    slot_first_cycles = {}
    for row in csv.DictReader((directory / "mshr.csv").open()):
        r = {key: int(value) for key, value in row.items()}
        c, slot = r["cycle"], r["slot"]
        slot_samples[slot] += 1
        slot_first_cycles.setdefault(slot,c)
        prev = previous.get(slot)
        if prev and c != prev["cycle"] + 1:
            errors.append(f"MSHR slot {slot}: nonconsecutive samples at {c}")
        if r["valid"]:
            if slot not in active:
                active[slot] = {"slot": slot, "start": c, "address": r["address"],
                                "left_censored": prev is None,
                                "preceding_init_request": bool(prev and prev["init_request"]),
                                "phase_cycles": collections.Counter()}
            active[slot]["phase_cycles"][r["phase"]] += 1
            if active[slot]["address"] != r["address"]:
                errors.append(f"MSHR slot {slot}: address changed during valid interval at {c}")
        elif slot in active:
            interval = active.pop(slot)
            interval.update(end=c, duration=c-interval["start"], right_censored=False)
            (censored if interval["left_censored"] else closed).append(interval)
        previous[slot] = r
    for slot, interval in active.items():
        interval.update(end=None, duration=previous[slot]["cycle"]+1-interval["start"], right_censored=True)
        censored.append(interval)
    pending, reads, unmatched, serial_reuse = collections.defaultdict(collections.deque), [], [], []
    request_count = response_count = 0
    request_cycles = []
    prev_event_cycle = None
    for row in csv.DictReader((directory / "backing_memory.csv").open()):
        c, serial = int(row["cycle"]), int(row["serial"])
        if prev_event_cycle is not None and c < prev_event_cycle:
            errors.append(f"Backing memory event cycles are out of order at {c}")
        prev_event_cycle = c
        if row["event"] == "read_request":
            request_count += 1
            request_cycles.append(c)
            if pending[serial]:
                serial_reuse.append({"cycle": c, "serial": serial})
            pending[serial].append({"cycle": c, "address": int(row["address"])})
        elif row["event"] == "read_response":
            response_count += 1
            if not pending[serial]:
                unmatched.append({"cycle": c, "serial": serial})
            else:
                req = pending[serial].popleft()
                if c <= req["cycle"]:
                    errors.append(f"Nonpositive backing read latency for serial {serial} at {c}")
                reads.append({"serial": serial, "request_cycle": req["cycle"], "response_cycle": c,
                              "address": req["address"], "duration": c-req["cycle"]})
        else:
            errors.append(f"Unknown backing-memory event {row['event']}")
    bad, valid_samples, monitor_mismatches = [], 0, []
    for row in csv.DictReader((directory / "predecode.csv").open()):
        r = {key: int(value) for key, value in row.items()}
        valid_samples += 1
        insn = r["instruction"]
        opcode = insn & 127
        allowed = opcode in {3,0x23,0x13,0x37,0x17,0x63,0x67,0x6f,0xf,0x73} or (opcode == 0x33 and insn >> 25 != 1)
        if allowed != bool(r["isa_allowed"]):
            monitor_mismatches.append(r)
        if not allowed:
            bad.append(r)
    phase_totals = collections.Counter()
    for interval in closed:
        phase_totals.update(interval["phase_cycles"])
    if request_count and not response_count:
        errors.append("Backing memory trace contains requests but no responses; monitor/trace is unusable for latency")
    if not valid_samples:
        errors.append("No valid predecode ISA samples")
    if len(set(slot_samples.values())) != 1 or len(set(slot_first_cycles.values())) != 1:
        errors.append("MSHR slots do not cover the same cycle interval")
    summary = {"trace_directory": str(directory.resolve()),
               "scope": "Empirical whole-run traces including startup, speculation and recovery; not a worst-case bound",
               "edge_convention": "Samples follow eval at rising edge c. MSHR valid is registered state; [first-valid c, first-invalid d) has d-c live cycles. Request ack and response valid are settled interface signals consumed at the next edge; paired latency is response-sample minus request-sample. No mixed-edge correction is applied.",
               "trace_sha256": {name:hashlib.sha256((directory/name).read_bytes()).hexdigest() for name in ('mshr.csv','backing_memory.csv','predecode.csv')},
               "mshr_slot_samples": slot_samples,
               "mshr_first_cycle": min(slot_first_cycles.values()) if slot_first_cycles else None,
               "mshr_last_cycle": max(r['cycle'] for r in previous.values()) if previous else None,
               "mshr_lifetime_cycles": stats([x["duration"] for x in closed]),
               "mshr_censored_intervals": censored,
               "mshr_closed_phase_totals": phase_totals,
               "mshr_wait_read_phase14_cycles_per_lifetime": stats([x["phase_cycles"].get(14,0) for x in closed]),
               "mshr_complete_phase18_cycles_per_lifetime": stats([x["phase_cycles"].get(18,0) for x in closed]),
               "backing_read_latency_cycles": stats([x["duration"] for x in reads]),
               "backing_scope": "All accepted backing reads, including instruction-cache traffic",
               "backing_read_requests": request_count, "backing_read_responses": response_count,
               "backing_min_observed_read_request_gap": min((b-a for a,b in zip(request_cycles,request_cycles[1:])),default=None),
               "backing_unmatched_responses": unmatched,
               "backing_serial_reuse_while_pending": serial_reuse,
               "backing_pending_at_end": {k:list(v) for k,v in pending.items() if v},
               "isa_valid_samples": valid_samples, "isa_disallowed_samples": len(bad),
               "isa_disallowed_distinct_pc_instruction": sorted({(r["pc"],r["instruction"]) for r in bad}),
               "isa_first_disallowed_samples": bad[:20],
               "isa_monitor_recompute_mismatches": monitor_mismatches,
               "trace_integrity_errors": errors}
    (directory / "mshr_lifetimes.json").write_text(json.dumps({"completed":closed,"censored":censored},indent=2)+'\n')
    (directory / "backing_read_latencies.json").write_text(json.dumps(reads,indent=2)+'\n')
    (directory / "lifetime_summary.json").write_text(json.dumps(summary,indent=2)+'\n')
    return summary

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("directories", type=Path, nargs="+")
    args=p.parse_args()
    integrity_ok=True
    for directory in args.directories:
        result=analyze(directory)
        integrity_ok &= not (result['trace_integrity_errors'] or result['backing_unmatched_responses']
                            or result['backing_serial_reuse_while_pending'] or result['isa_monitor_recompute_mismatches'])
        print(directory.name, "MSHR", result["mshr_lifetime_cycles"],
              "read", result["backing_read_latency_cycles"],
              "ISA violations", result["isa_disallowed_samples"],
              "unmatched responses", len(result["backing_unmatched_responses"]),
              "trace integrity errors",result['trace_integrity_errors'])
    return 0 if integrity_ok else 1

if __name__=="__main__":
    raise SystemExit(main())
