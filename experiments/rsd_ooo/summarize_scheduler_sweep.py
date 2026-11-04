#!/usr/bin/env python3
"""Audit legal one-variable ROB/IQ capacity changes against retained baseline runs."""
import argparse
import csv
import hashlib
import json
import math
from pathlib import Path
import re
from run_applications import validate
from summarize_applications import normalized_serial
from rsd_log_checks import assertion_diagnostics,diagnostic_categories

ROOT=Path(__file__).resolve().parent
R=ROOT/'results'
VARIANTS={'rob32_iq16':(32,16),'rob16_iq16':(16,16),'rob64_iq32':(64,32),'rob64_iq64':(64,64)}

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def load(path,group):
    data=json.loads((path/'summary.json').read_text())
    rows=data['tests'] if group=='upstream' else data
    index={r['test'] if group=='upstream' else r['name']:r for r in rows}
    assert len(index)==len(rows)
    return index

def audit(path,group,row):
    assert json.loads((path/'result.json').read_text())==row
    assert sha(path/'code.hex')==row['input_sha256']
    log_path=path/('simulation.log' if group=='upstream' else 'run.log')
    if 'log_sha256' in row:
        assert sha(log_path)==row['log_sha256']
    log=log_path.read_text(errors='replace')
    assert 'PC reached PC_GOAL:' in log and not re.search(r'Assertion failed|%Error|Exception caused',log)
    categories=diagnostic_categories(log)
    assert not categories['other_named_assertions'],('Named RSD invariant diagnostic',path,categories)
    if group!='upstream':
        assert not categories['progress_watchdogs'],('Unexpected progress watchdog in completed positive run',path)
    cycles=row['cycles'] if group=='upstream' else row['counters']['Elapsed cycles']
    assert re.findall(r'^Elapsed cycles:\s*(\d+)$',log,re.M)==[str(cycles)]
    if group=='upstream':
        assert (row.get('exit_code')==0 and row['pc_goal_reached'] and
                not row['register_mismatches'] and row['serial_exact_match'])
        if (path/'serial.ref.txt').exists():
            assert (path/'serial.out.txt').read_bytes().replace(b'\r',b'')==(path/'serial.ref.txt').read_bytes().replace(b'\r',b'')
    else:
        assert row['status']=='passed' and row['returncode']==0 and row['within_cycle_limit']
        if group=='diagnostics':
            assert (path/'serial.out.txt').read_bytes()==row['expected_serial'].encode()
        else:
            checks,roi=validate(row['name'],(path/'serial.out.txt').read_text(),row['iterations'])
            assert all(checks.values()) and roi==row['roi_cycles']
    return cycles

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--results-root',type=Path,default=R/'scheduler_sweep')
    args=p.parse_args()
    baseline={'upstream':R/'upstream_monitored_lq16_sq16',
              'diagnostics':R/'kernels_monitored16','applications':R/'apps_lq16_sq16'}
    base={g:load(p,g) for g,p in baseline.items()}
    assert {g:len(v) for g,v in base.items()}=={'upstream':8,'diagnostics':12,'applications':2}
    rows=[]
    source_changes={}
    for variant,(rob,iq) in {'rob64_iq16':(64,16),**VARIANTS}.items():
        paths=baseline if variant=='rob64_iq16' else {g:args.results_root/variant/g for g in base}
        if variant!='rob64_iq16':
            suite=json.loads((args.results_root/variant/'suite.json').read_text())
            manifest=suite['configuration']
            assert len(suite['groups'])==3
            assert manifest['rob']==rob and manifest['iq']==iq and manifest['lq']==manifest['sq']==16
            assert manifest['mshr']==2 and manifest['integer_physical_registers']==manifest['fp_physical_registers']==64
            assert manifest['replay_queue_entries']==20 and manifest['fetch_rename_commit_width']==2
            assert manifest['candidate'] is None and manifest.get('fp_candidate') is None
            assert sha(Path(suite['binary']))==manifest['binary_sha256']
            changes=[]
            src=Path(manifest['cwd'])
            for original in (ROOT/'rsd/Processor/Src').rglob('*.sv'):
                relative=original.relative_to(ROOT/'rsd/Processor/Src')
                if sha(original)!=sha(src/relative):
                    changes.append(str(relative))
            assert set(changes)=={'MicroArchConf.sv','SysDeps/Verilator/VerilatorHelper.sv'}
            source_changes[variant]=changes
        for group,path in paths.items():
            actual=load(path,group)
            assert set(actual)==set(base[group])
            for name,row in actual.items():
                run=path/(name.replace('/','_') if group=='upstream' else name)
                # New runners distinguish correct architectural completion
                # from named progress-watchdog diagnostics. Older retained
                # results predate that separate field; audit() rechecks them.
                passed=row.get('architectural_checks_passed',row['passed']) if group=='upstream' else row['status']=='passed'
                if passed:
                    whole=audit(run,group,row)
                else:
                    # Failed experiments remain evidence, never successful ratios.
                    assert json.loads((run/'result.json').read_text())==row
                    assert sha(run/'code.hex')==row['input_sha256']
                    log_path=run/('simulation.log' if group=='upstream' else 'run.log')
                    assert sha(log_path)==row['log_sha256']
                    log=log_path.read_text(errors='replace')
                    whole=row.get('cycles') if group=='upstream' else row.get('counters',{}).get('Elapsed cycles')
                    if whole is not None:
                        assert re.findall(r'^Elapsed cycles:\s*(\d+)$',log,re.M)==[str(whole)]
                reference=base[group][name]
                assert row['input_sha256']==reference['input_sha256']
                if group=='applications' and passed:
                    assert normalized_serial(name,row['observed_serial'])==normalized_serial(name,reference['observed_serial'])
                measured=row['roi_cycles'] if group=='applications' else whole
                reference_cycles=reference['roi_cycles'] if group=='applications' else (reference['cycles'] if group=='upstream' else reference['counters']['Elapsed cycles'])
                traces={f:sha(run/f) for f in ('resource.csv','memory_events.csv') if (run/f).exists()}
                raw_log=run/('simulation.log' if group=='upstream' else 'run.log')
                diagnostics=diagnostic_categories(raw_log.read_text(errors='replace'))
                rows.append({'variant':variant,'rob':rob,'iq':iq,'lq':16,'sq':16,'mshr':2,
                             'group':group,'workload':name,'cycles':measured,'whole_program_cycles':whole,
                             'cycle_scope':'mcycle benchmark-loop delta' if group=='applications' else 'upstream zero-based terminal cycle',
                             'cycle_ratio_vs_baseline':measured/reference_cycles if passed and measured is not None else None,'passed':passed,
                             'strict_runner_passed':row['passed'] if group=='upstream' else row['status']=='passed',
                             'failure_details':None if passed else {k:row.get(k) for k in ('status','pc_goal','within_cycle_limit','returncode','validation')},
                             'named_diagnostic_messages':sorted(set(diagnostics['named_messages'])),
                             'progress_watchdog_observed':bool(diagnostics['progress_watchdogs']),
                             'input_sha256':row['input_sha256'],'trace_sha256':traces,'result':str(run/'result.json')})
    aggregates=[]
    for variant in VARIANTS:
        for group in base:
            selected=[r for r in rows if r['variant']==variant and r['group']==group]
            complete=all(r['passed'] for r in selected)
            ratios=[r['cycle_ratio_vs_baseline'] for r in selected if r['passed']]
            aggregates.append({'variant':variant,'group':group,'cases':len(selected),'passed':len(ratios),
                               'geomean_cycle_ratio':math.exp(sum(map(math.log,ratios))/len(ratios)) if complete else None,
                               'min_cycle_ratio':min(ratios) if complete else None,'max_cycle_ratio':max(ratios) if complete else None})
    failed=[r for r in rows if not r['passed']]
    report={'audit_passed':True,'all_runs_functionally_passed':not failed,'new_executions':88,'reused_baseline_executions':22,
            'new_passed':88-len(failed),'new_failed':len(failed),
            'scope':'Independent ROB shrink64/32/16 or IQ growth16/32/64; all other explicit capacities and execution widths fixed. Functional/timing capacity controls, not cycle-equivalent Pscorr.',
            'unsupported':'IQ4 violates8-bank free-list RAM divisibility. IQ8 gives one-entry-bank reversed address slices and zero-bit reset-counter dimensions; no primitive fixes or port changes are silently introduced.',
            'raw_occupancy_note':'Resource traces include reset/freelist initialization; whole-trace IQ peak must not be described as application demand.',
            'upstream_diagnostic_qualification':'CacheFlush/Fence can print >500-cycle progress-watchdog messages and subsequently complete with expected registers/output. These are retained separately; architectural passes do not imply zero internal diagnostics. One unnamed assertion is not retrospectively identifiable.',
            'processor_sv_files_changed':source_changes,'aggregates':aggregates,'rows':rows}
    (args.results_root/'summary.json').write_text(json.dumps(report,indent=2)+'\n')
    with (args.results_root/'comparison.csv').open('w',newline='') as f:
        fields=[k for k in rows[0] if k not in ('trace_sha256','failure_details','named_diagnostic_messages')];w=csv.DictWriter(f,fieldnames=fields,extrasaction='ignore');w.writeheader();w.writerows(rows)
    print(json.dumps({'audit_passed':True,'new_executions':88,'new_failed':len(failed),'baseline_reused':22,'aggregates':aggregates},indent=2))

if __name__=='__main__':
    main()
