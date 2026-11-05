#!/usr/bin/env python3
"""Compare ROM fetch payloads, faults and pipeline behavior with a native trace.

Finite validation of the external instruction model, not an occupancy theorem.
Instruction ROM is immutable. This audit also checks that the recorded native
program never writes into its image; that finite fact is not a universal premise
about the core or an assumption inserted into the proof.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path

from analyze_fetch_spacing import native_edges
from program_rom import read_image, response


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audit(rows, image, gap):
    stages = None
    cooldown = 0
    checks, returns, faults, canceled = 0, 0, 0, 0
    zero = (0, 0, False, 0)
    for row in rows:
        if stages is not None:
            valid, data, fault, code = stages[1]
            for key, expected in (('fetch_response_valid', valid), ('fetch_data', data),
                                  ('fetch_exception', int(fault)), ('fetch_exception_code', code)):
                if row[key] != expected:
                    raise ValueError(f"ROM recurrence mismatch at {row['cycle']}: {key}={row[key]} expected {expected}")
            if row['reset_n']:
                expected_grant = row['fetch_response_ready'] and cooldown == 0
                if row['core_gnt'] != expected_grant:
                    raise ValueError(f"Grant mismatch at {row['cycle']}")
                checks += 1
                returns += bool(valid and row['fetch_response_ready'])
                faults += bool(valid and row['fetch_response_ready'] and fault)
                if row['store_req'] and row['store_grant']:
                    # All image bytes are mapped contiguously from zero. Include
                    # every active byte lane, including a partially overlapping store.
                    for byte in range(8):
                        if (row['store_be'] >> byte) & 1:
                            if 0 <= row['store_addr'] + byte < image['bytes']:
                                raise ValueError('Recorded store modifies the instruction image')
        if not row['reset_n']:
            stages = [zero, zero]
            cooldown = 0
            continue
        if stages is None:
            continue  # Source simulation startup before the first reset.
        accepted = bool(row['core_req'] and row['core_gnt'])
        gate = cooldown == 0
        cooldown = gap-1 if accepted else max(0, cooldown-1)
        if row['flush']:
            canceled += bool(stages[0][0]) + bool(accepted)
            stages = [zero, zero]
        elif row['fetch_response_ready']:
            request = bool(row['core_req'] and gate)
            data, fault, code = response(image, row['fetch_addr']) if request else (0, False, 31)
            stages = [(int(request), data, fault, code), stages[0]]
    return {'active_edges_checked': checks, 'returned_fetches_checked': returns,
            'instruction_faults': faults, 'all_fetch_payload_fault_code_and_handshake_checks_passed': True,
            'recorded_stores_disjoint_from_instruction_image': True,
            'limits': 'Finite trace validation only; ROM is the declared immutable instruction platform. This does not prove arbitrary future stores are disjoint in the unified native testbench.'}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--image', type=Path, required=True)
    ap.add_argument('--vcd', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--gap', type=int, default=2)
    args = ap.parse_args()
    if args.output.exists() or args.gap < 1:
        ap.error('Use a fresh output path and a positive gap')
    image = read_image(args.image)
    base = 'TOP.tb_bare.u_datapath.'
    rows = native_edges(args.vcd, {'fetch_data':base+'instr_rdata_i',
        'store_req':base+'data_store_req_o', 'store_grant':base+'data_store_gnt_i',
        'store_addr':base+'data_store_addr_o', 'store_be':base+'data_store_be_o'})
    result = audit(rows, image, args.gap)
    result.update(image_sha256=sha(args.image), raw_vcd_sha256=sha(args.vcd),
        script_sha256=sha(Path(__file__)), rom_helper_sha256=sha(Path(__file__).with_name('program_rom.py')),
        observer_sha256=sha(Path(__file__).with_name('analyze_fetch_spacing.py')), gap=args.gap)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
