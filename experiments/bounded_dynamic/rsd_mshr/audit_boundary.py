#!/usr/bin/env python3
"""Check the final native MSHR/ID-allocator boundary and preserve source evidence."""
import argparse
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
REVISION = '7b65f6ba0bce58d4d859082660123b7100aae975'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rsd', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise SystemExit('Refusing existing audit output')
    base = HERE/'results/baseline_v5'
    manifest = json.loads((base/'manifest.json').read_text())
    assert manifest['status'] == 'complete' and manifest['rsd_revision'] == REVISION
    for name, expected in manifest['source_sha256'].items():
        assert sha(base/'src'/name) == expected
    wrapper = (base/'MshrObserved.sv').read_text()
    assert wrapper == (HERE/'MshrObserved.sv').read_text()
    assert 'read_busy_external' not in wrapper
    for connection in ['.memAccessReadBusy(free_empty)', '.push(response_valid)',
                       '.pop(read_accept && !free_empty)', '.pushedData(response_id)',
                       '.headData(allocated_id)', '.memReadSerial(response_id)',
                       '.memReadDataReady(response_valid)',
                       '.SIZE(1 << MEM_ACCESS_SERIAL_BIT_SIZE)',
                       '.ENTRY_WIDTH(MEM_ACCESS_SERIAL_BIT_SIZE)']:
        assert connection in wrapper
    assert 'ic_ack = {bus.icMemAccessReqAck.ack, bus.icMemAccessReqAck.serial};' in wrapper
    assert not any(word in wrapper for word in ['assume(', 'assert(', 'cover('])

    # The entire second boundary correction is the removal of the added stall
    # input and its OR gate. It does not change any component module or state.
    old4 = (HERE/'results/baseline_v4/MshrObserved.sv').read_text()
    assert old4.replace('input logic read_busy_external, write_busy,',
                        'input logic write_busy,').replace(
                            '.memAccessReadBusy(read_busy_external || free_empty)',
                            '.memAccessReadBusy(free_empty)') == wrapper
    design = json.loads((base/'baseline.json').read_text())['modules']['MshrObserved']
    assert sum(len(p['bits']) for p in design['ports'].values() if p['direction'] == 'input') == 631
    assert sum(len(p['bits']) for p in design['ports'].values() if p['direction'] == 'output') == 545
    assert all(b not in ('x', 'z') for p in design['ports'].values() for b in p['bits'])
    assert len(design['ports']['ic_ack']['bits']) == 3
    assert sum(len(c['connections']['Q']) for c in design['cells'].values() if c['type'] == '$dff') == 343
    assert sum(c['type'] == '$eq' for c in design['cells'].values()) == 42

    args.output.mkdir(parents=True)
    evidence = {}
    # These files justify composition/consumer facts but are not additional
    # hardware compiled into the component.
    for name in ['Memory/Axi4Memory.sv', 'Cache/ICache.sv', 'Core.sv']:
        data = subprocess.check_output(['git', '-C', str(args.rsd.resolve()), 'show',
                                        REVISION+':Processor/Src/'+name])
        assert data == (args.rsd/'Processor/Src'/name).read_bytes()
        target = args.output/'source_context'/name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        evidence[name] = sha(target)
    icache = (args.output/'source_context/Cache/ICache.sv').read_text()
    assert 'icMemAccessReqAck.wserial' not in icache
    assert 'icMemAccessReqAck.ack' in icache and 'icMemAccessReqAck.serial' in icache
    axi = (args.output/'source_context/Memory/Axi4Memory.sv').read_text()
    for source in ['assign memAccessReadBusy = readReqIDFreeListEmpty;',
                   'assign pushFreeReadReqID = memReadDataReady;',
                   'assign pushedFreeReadReqID = memoryReadDataID;',
                   'assign popFreeReadReqID = (~readReqIDFreeListEmpty && memAccessRE)',
                   'assign nextMemReadSerial = popedFreeReadReqID;',
                   'assign memReadSerial = memoryReadDataID;']:
        assert source in axi

    a = json.loads((HERE/'results/baseline_v3/baseline.json').read_text())['modules']['MshrObserved']
    b = json.loads((HERE/'results/baseline_v4/baseline.json').read_text())['modules']['MshrObserved']
    assert set(a['cells']) == set(b['cells'])
    for name, cell in a['cells'].items():
        assert {k:v for k,v in cell.items() if k != 'attributes'} == {
            k:v for k,v in b['cells'][name].items() if k != 'attributes'}
    assert all(p == b['ports'][n] for n,p in a['ports'].items() if n != 'ic_ack')
    assert a['ports']['ic_ack']['bits'] == ['x']+b['ports']['ic_ack']['bits']
    report = {
        'status': 'passed', 'baseline': 'results/baseline_v5',
        'baseline_json_sha256': sha(base/'baseline.json'),
        'baseline_verilog_sha256': sha(base/'baseline.v'),
        'baseline_manifest_sha256': sha(base/'manifest.json'),
        'wrapper_sha256': sha(base/'MshrObserved.sv'),
        'source_context_sha256': evidence,
        'input_bits': 631, 'defined_output_bits': 545,
        'flip_flop_bits': 343, 'equality_cells': 42,
        'native_free_list': {'entries': 4, 'id_width': 2,
            'busy': 'empty', 'push': 'response_valid', 'push_data': 'response_id',
            'pop': 'read_accept && !empty', 'next_id': 'headData'},
        'assumptions': 'Common synchronous reset; external read transaction contract only in formal monitor',
        'boundary': 'All defined functional outputs of actual handler/arbiter/mux/controller plus actual read-ID FreeList; arbitrary surrounding cache/recovery/write inputs; not a full AXI controller or full OoO core',
        'excluded_undefined_field': 'icMemAccessReqAck.wserial: original MemoryAccessController never assigns it; ICache only reads ack/serial',
        'historical_v3_to_v4': 'All 553 cells and all other ports identical; only raw unassigned ic_ack[0] omitted',
        'historical_v4_to_v5': 'Removed external read_busy input and extra OR gate; original busy=free_empty composition restored',
        'historical_negative_scope': 'negative_deadline_v1 and negative_order_v1 use baseline_v3 with the extra external read-busy input; final two-copy negatives must use baseline_v5',
    }
    (args.output/'summary.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
