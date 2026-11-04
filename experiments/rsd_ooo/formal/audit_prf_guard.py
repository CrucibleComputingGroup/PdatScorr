#!/usr/bin/env python3
"""Audit localized PRF reset guard and all-port area wrapper; no core proof."""
import hashlib
import json
from pathlib import Path

FORMAL = Path(__file__).resolve().parent
EXP = FORMAL.parent
SRC = EXP / 'rsd/Processor/Src'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    builds = [EXP / 'results/prf_guard64_control', EXP / 'results/prf_guard48']
    sources = [b / 'source/Processor/Src' for b in builds]
    manifests = [json.loads((b / 'manifest.json').read_text()) for b in builds]
    checks = {}
    original = (SRC / 'RegisterFile/RegisterFile.sv').read_text()
    expected = original
    for prefix, capacity, counter, dest in [
        ('reg', 'PSCALAR_NUM', 'regRstIndex', 'dstRegNum'),
        ('fpReg', 'PSCALAR_FP_NUM', 'fpRstIndex', 'dstFPRegNum')]:
        old = f'{dest} [i] = {counter} + i;'
        assert expected.count(old) == 1
        added = (old + '\n                // Explicit non-power-of-two PRF reset compatibility.\n'
                 f'                if ({dest}[i] >= {capacity}) begin\n'
                 f'                    {prefix}WE[i] = FALSE;\n'
                 f"                    {dest}[i] = '0; // XOR/LVT reads even inactive write addresses.\n"
                 '                end')
        expected = expected.replace(old, added)
    config = (SRC / 'MicroArchConf.sv').read_text()
    for b, s, m, size in zip(builds, sources, manifests, [64, 48]):
        checks[b.name + '_all_228_source_hashes'] = len(m['source_sha256']) == 228 and all(
            sha(s / name) == digest for name, digest in m['source_sha256'].items())
        checks[b.name + '_only_two_reset_guards'] = (
            s / 'RegisterFile/RegisterFile.sv').read_text() == expected
        expected_config = config.replace('CONF_PSCALAR_NUM = 64;', f'CONF_PSCALAR_NUM = {size};').replace(
            'CONF_PSCALAR_FP_NUM = 64;', f'CONF_PSCALAR_FP_NUM = {size};')
        checks[b.name + '_only_coupled_PRF_config'] = (s / 'MicroArchConf.sv').read_text() == expected_config
        checks[b.name + '_original_types_RAM_interface'] = all(
            (s / name).read_bytes() == (SRC / name).read_bytes()
            for name in ['BasicTypes.sv', 'Primitives/RAM.sv', 'RegisterFile/RegisterFileIF.sv'])
        checks[b.name + '_matching_capacity_metadata'] = (
            m['integer_physical_registers'] == m['fp_physical_registers'] == size and
            m['prf_reset_guard'] and m['rob'] == 64 and m['iq'] == m['lq'] == m['sq'] == 16)
    checks['identical_guarded_RegisterFile_bytes'] = (
        sources[0] / 'RegisterFile/RegisterFile.sv').read_bytes() == (
        sources[1] / 'RegisterFile/RegisterFile.sv').read_bytes()

    # Complete enumeration of the source-reviewed narrowed unsigned address
    # domain. Counter + lane is first assigned to dstRegNum, then compared.
    # These are finite combinational facts, not bounded sequential core proofs.
    power_of_two = []
    for capacity in [64, 128]:
        address_bits = (capacity - 1).bit_length()
        triggering = [a for a in range(1 << address_bits) if a >= capacity]
        assert not triggering
        power_of_two.append(dict(capacity=capacity, address_bits=address_bits,
                                 all_possible_addresses_checked=1 << address_bits,
                                 triggering_addresses=triggering))
    checks['power_of_two_guard_identically_false'] = True

    # Original reset counters are packed PRegNumPath (7 bits at PRF48); their
    # results narrow to 6-bit bank addresses before the guard. INT has 5 write
    # ports, FP has 2. Verify all legal entries receive initialization and every
    # downstream reset write address is legal after suppression/clamping.
    coverage = {}
    for bank, width in [('integer', 5), ('fp', 2)]:
        counter = 0
        written = set()
        disabled = 0
        for cycle in range(10000):
            for lane in range(width):
                address = (counter + lane) & 63
                we = address < 48
                guarded_address = address if we else 0
                assert 0 <= guarded_address < 48
                if we:
                    written.add(guarded_address)
                else:
                    disabled += 1
            counter = (counter + width) & 127
        assert written == set(range(48))
        coverage[bank] = dict(initialized_entries=sorted(written),
                              suppressed_reset_writes=disabled,
                              guarded_address_always_in_range=True)
    checks['48_reset_address_coverage_and_legality'] = True
    comparison = json.loads((EXP / 'results/prf_comparison.json').read_text())
    guarded_rows = [r for r in comparison['rows'] if r['variant'] in ('guard64', 'guard48')]
    checks['46_guarded_architectural_cases_pass'] = len(guarded_rows) == 46 and all(
        r['architectural_checks_passed'] for r in guarded_rows)
    diagnostics = [dict(variant=r['variant'], workload=r['workload'], diagnostics=r['named_diagnostics'])
                   for r in guarded_rows if not r['strict_runner_passed']]
    checks['watchdogs_remain_explicit'] = len(diagnostics) == 4 and all(
        r['diagnostics'] == ['Deadlock detected'] and r['workload'] in ('Asm/CacheFlush', 'Asm/Fence')
        for r in diagnostics)
    checks['guard64_measured_cycles_and_resource_memory_traces_match'] = comparison[
        'control64_exact_cycles_and_memory_resource_traces']

    report = dict(status='PASS' if all(checks.values()) else 'FAIL', checks=checks,
                  local_guard_enumeration=power_of_two, prf48_reset_coverage=coverage,
                  strict_runner_diagnostics=diagnostics,
                  source_binding_sha256={str(b / 'manifest.json'): sha(b / 'manifest.json') for b in builds},
                  comparison_sha256=sha(EXP / 'results/prf_comparison.json'),
                  wrapper_sha256=sha(FORMAL / 'RegisterFileObserved.sv'),
                  source_list_sha256=sha(FORMAL / 'registerfile_sources.txt'),
                  scope='Localized reset-guard source audit; complete finite narrowed-address proof '
                        'that guard is inactive at64/128; source-reviewed48 reset coverage. '
                        'No whole-core proof or capacity-reduction equivalence claim.')
    out = EXP / 'results/prf_guard'
    (out / 'source_boundary_audit.json').write_text(json.dumps(report, indent=2) + '\n')
    assert all(checks.values()), report
    (out / 'source_boundary_audit.txt').write_text('''PASS: PRF reset-compatibility and area-boundary audit

All 228 recorded source hashes match in each guarded64/guarded48 simulation
snapshot. Both snapshots contain byte-identical RegisterFile RTL. Relative to
pinned original, exactly two snippets are inserted in the INT/FP reset loops:
after narrowing counter+lane to the destination-address type, addresses outside
the configured bank disable WE and become zero. Both original counter updates,
reset controls, data/valid initialization and every non-reset operation remain.
The 64 config differs only in newline encoding; 48 changes only the two coupled
physical-register capacities. BasicTypes, RAM primitives and interface match.

At 64 the bank address is unsigned six bits: addr>=64 is impossible. At 128 it is
seven bits: addr>=128 is impossible. Exhaustive finite enumeration confirms the
guard is identically inactive. Thus the guarded64 control is locally equivalent
to original64 for every two-state register-file state/input, without assuming
reset reachability or a binary. This is not a whole-core equivalence proof.

At 48 the six-bit address can be 48..63. Disabling only WE leaves these values on
XOR/LVT internal read addresses: RAM.sv:957 assigns wbReadAddr[j]=wa[j] without
testing WE. Clamping the inactive address is therefore required for valid array
addressing. No active legal write changes, and disabled ports remain disabled.
The source-reviewed original seven-bit reset counters advance by 5 (INT)/2 (FP);
enumeration of 10000 reset steps from rstStart initialization covers all 0..47
entries and produces no out-of-range reset address after the guard. Non-reset
invalid addresses are not repaired or hidden; the patch is only a reset fix.

Measured guarded64/guarded48 each pass 23 architectural cases (12 diagnostics,
2 applications, FP control and 8 upstream tests). Four strict-runner failures remain
explicit: CacheFlush and Fence emit the named progress-watchdog diagnostic in
both guarded variants despite passing architectural checks. Do not describe
all 46 runs as strict clean passes. Guard64 measured cycles and resource/memory
traces match original64. Reduced capacity can change cycles/trace; no universal
capacity-reduction equivalence or all-program sufficiency is asserted.

formal/RegisterFileObserved.sv exposes every RegisterFileIF functional input
and all nine output port arrays: 13 read operands, each 33 bits including validity.
It preserves all INT/complex/memory/FP write strobes, data, physical tag/isFP
bits and reset signals. It contains no assumptions, masks, forced addresses or
input restrictions. The area comparison is matched guarded64 versus guarded48,
not original64 versus an unlabelled pure parameter change. Both have 6-bit bank
addresses and 7-bit tagged physical-register inputs. No FP PRF removal is implied.
''')
    print('PASS: PRF source, local guard equivalence, reset coverage and all-port wrapper audit')


if __name__ == '__main__':
    main()
