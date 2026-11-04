#!/usr/bin/env python3
"""Audit coupled PRF growth and separately labelled reset-compatibility controls."""
import csv
import json
from pathlib import Path
from summarize_scheduler_sweep import audit,load,sha
from summarize_applications import normalized_serial
from rsd_log_checks import diagnostic_categories

ROOT=Path(__file__).resolve().parent
R=ROOT/'results'

def main():
    base_paths={'upstream':R/'upstream_monitored_lq16_sq16','diagnostics':R/'kernels_monitored16',
                'applications':R/'apps_lq16_sq16','fp_control':R/'fp_scheduler/base/fp_control'}
    variants={'prf128':(128,False,R/'prf_growth/prf128',R/'prf_growth/prf128_fp_control'),
              'guard64':(64,True,R/'prf_guard/control64',R/'prf_guard/control64_fp'),
              'guard48':(48,True,R/'prf_guard/guard48',R/'prf_guard/guard48_fp')}
    rows=[]
    for name,(capacity,guard,folder,fp_folder) in variants.items():
        suite=json.loads((folder/'suite.json').read_text())
        manifest=suite['configuration'];src=Path(manifest['cwd'])
        assert manifest['integer_physical_registers']==manifest['fp_physical_registers']==capacity
        assert manifest['rob']==64 and manifest['iq']==manifest['lq']==manifest['sq']==16 and manifest['mshr']==2
        assert bool(manifest.get('prf_reset_guard',False))==guard
        assert sha(Path(suite['binary']))==manifest['binary_sha256']
        changed=[]
        for original in (ROOT/'rsd/Processor/Src').rglob('*.sv'):
            relative=original.relative_to(ROOT/'rsd/Processor/Src')
            if sha(original)!=sha(src/relative):changed.append(str(relative))
        expected_changes={'MicroArchConf.sv','SysDeps/Verilator/VerilatorHelper.sv'}
        if guard:expected_changes.add('RegisterFile/RegisterFile.sv')
        assert set(changed)==expected_changes
        # MicroArchConf's upstream CRLF is normalized by the isolated builder,
        # including the unchanged64control; inspect numeric configuration too.
        for group,base_path in base_paths.items():
            kind='upstream' if group=='fp_control' else group
            path=fp_folder if group=='fp_control' else folder/group
            base=load(base_path,kind);actual=load(path,kind)
            assert set(base)==set(actual)
            for case,row in actual.items():
                run=path/(case.replace('/','_') if kind=='upstream' else case)
                whole=audit(run,kind,row)
                reference=base[case]
                assert row['input_sha256']==reference['input_sha256']
                measured=row['roi_cycles'] if group=='applications' else whole
                base_cycles=reference['roi_cycles'] if group=='applications' else (reference['cycles'] if kind=='upstream' else reference['counters']['Elapsed cycles'])
                if group=='applications':
                    assert normalized_serial(case,row['observed_serial'])==normalized_serial(case,reference['observed_serial'])
                log_path=run/('simulation.log' if kind=='upstream' else 'run.log')
                named=diagnostic_categories(log_path.read_text(errors='replace'))
                baseline_run=base_path/(case.replace('/','_') if kind=='upstream' else case)
                if group=='applications':
                    # Original application baseline was uninstrumented. The
                    # separately validated no-FP baseline has identical RTL,
                    # images and cycles and supplies raw observation traces.
                    baseline_run=R/'fp_scheduler/base/applications'/case
                    monitor_reference=json.loads((baseline_run/'result.json').read_text())
                    assert monitor_reference['input_sha256']==reference['input_sha256']
                    assert monitor_reference['counters']==reference['counters']
                trace_match={f:sha(run/f)==sha(baseline_run/f) for f in ('resource.csv','memory_events.csv') if (baseline_run/f).exists()}
                if name=='guard64':
                    assert measured==base_cycles and whole==(reference['cycles'] if kind=='upstream' else reference['counters']['Elapsed cycles'])
                    assert all(trace_match.values())
                rows.append({'variant':name,'integer_prf':capacity,'fp_prf':capacity,'reset_guard_rtl_change':guard,
                             'group':group,'workload':case,'architectural_checks_passed':True,
                             'strict_runner_passed':row['passed'] if kind=='upstream' else row['status']=='passed',
                             'named_diagnostics':sorted(set(named['named_messages'])),
                             'cycles':measured,'whole_program_cycles':whole,'cycle_ratio_vs_original64':measured/base_cycles,
                             'cycle_scope':'mcycle benchmark-loop delta' if group=='applications' else 'zero-based terminal cycle',
                             'same_baseline_resource_memory_traces':trace_match,'trace_baseline':str(baseline_run),
                             'input_sha256':row['input_sha256'],'result':str(run/'result.json')})
    assert len(rows)==69
    result={'audit_passed':True,'new_executions':69,'architectural_passes':69,
            'strict_runner_failures':sum(not r['strict_runner_passed'] for r in rows),
            'named_watchdog_cases':sum(bool(r['named_diagnostics']) for r in rows),
            'scope':'PRF128/128 is a pure coupled-parameter growth control. PRF48/48 requires the explicit reset-write/address guard RTL compatibility change; guard64 is the matched control, not an unmodified-source claim.',
            'control64_exact_cycles_and_memory_resource_traces':True,
            'diagnostic_qualification':'Upstream CacheFlush/Fence can emit named500-cycle progress watchdogs and still reach goal with correct state. Strict flags and all messages remain visible. Empty unnamed assertion not retrospectively identifiable.',
            'rows':rows}
    (R/'prf_comparison.json').write_text(json.dumps(result,indent=2)+'\n')
    with (R/'prf_comparison.csv').open('w',newline='') as f:
        fields=[k for k in rows[0] if k not in ('named_diagnostics','same_baseline_resource_memory_traces')]
        writer=csv.DictWriter(f,fieldnames=fields,extrasaction='ignore');writer.writeheader();writer.writerows(rows)
    print(json.dumps({'audit_passed':True,'new_executions':69,'architectural_passes':69,
                      'strict_runner_failures':result['strict_runner_failures'],
                      'applications':[r for r in rows if r['group']=='applications']},indent=2))

if __name__=='__main__':
    main()
