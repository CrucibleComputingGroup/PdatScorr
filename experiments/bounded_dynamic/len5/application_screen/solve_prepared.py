#!/usr/bin/env python3
"""Run one solver on an already inspected immutable admission query.

Preparation and solver artifacts stay separate. Bounded success never becomes
an unbounded certificate, and imported theorem dependencies are checked again.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE.parents[3]), str(HERE)]
from odc.temporal import digest, run_command


def require(condition, message):
    if not condition: raise ValueError(message)


def validate_prepared(directory):
    directory = Path(directory).resolve()
    summary = json.loads((directory/'summary.json').read_text())
    require(summary['status'] == 'prepared_query_only' and summary['accepted_optimization'] is False,
            'Only an inspected preparation may be solved')
    for key, name in [('source_json','source.json'), ('core','core.v'), ('core_json','core.json'),
        ('harness','AdmissionScreen.sv'), ('script','formal_screen.py'), ('temporal_helper','temporal.py'),
        ('rom_helper','program_rom.py'), ('rom_image','program.hex'), ('aig','screen.aig')]:
        require(digest(directory/name) == summary[key+'_sha256'], 'Prepared artifact changed: '+name)
    require(Path(summary['query_core_path']).resolve().parent == directory, 'Query model is outside its preparation')
    require(digest(Path(summary['query_core_path'])) == summary['query_core_sha256'], 'Prepared query-only model changed')
    if summary.get('native_word_domain_import'):
        from domain_lemmas import verify_dependencies as verify_words
        from rom_domain_import import verify_dependencies as verify_rom
        verify_words(summary['native_word_domain_import'])
        verify_rom(summary['external_rom_domain_import'])
        require(summary['query_property_counts'] == {'assert':3,'assume':8,'cover':0}, 'Composed property inventory changed')
    else:
        require(summary['query_property_counts'] == {'assert':3,'assume':1,'cover':0}, 'Property inventory changed')
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepared', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--engine', choices=('pdr','bmc'), required=True)
    parser.add_argument('--frames', type=int, default=64)
    parser.add_argument('--timeout', type=int, default=120)
    parser.add_argument('--abc', default='/usr/local/bin/abc')
    args = parser.parse_args()
    require(args.frames > 0 and args.timeout > 0, 'Positive solver budget and bounded horizon required')
    prepared = args.prepared.resolve(); summary = validate_prepared(prepared)
    out = args.output.resolve(); out.mkdir(parents=True, exist_ok=False)
    (out/'solve_prepared.py').write_bytes(Path(__file__).read_bytes())
    summary_hash = digest(prepared/'summary.json'); script_hash = digest(Path(__file__))
    aig = prepared/'screen.aig'
    action = f'pdr -T {args.timeout} -v' if args.engine == 'pdr' else f'bmc3 -F {args.frames} -T {args.timeout} -v'
    command = f'read_aiger "{aig}"; fold; orpos; {action}; write_cex -a "{out/"counterexample.aiw"}"'
    record = {'status':'running', 'accepted_optimization':False, 'engine':args.engine,
        'prepared_directory':str(prepared), 'prepared_summary_sha256':summary_hash,
        'aig_sha256':digest(aig), 'query_property_counts':summary['query_property_counts'],
        'script_sha256':script_hash, 'requested_seconds':args.timeout,
        'requested_frames':args.frames if args.engine == 'bmc' else None,
        'scope':'Original three safety obligations with certified decoder and seven proved instruction-domain lemmas; no admission premise'}
    execution = run_command([args.abc,'-c',command], out/(args.engine+'.log'), args.timeout+5)
    record['execution'] = execution; record['status'] = 'unknown'
    log = (out/(args.engine+'.log')).read_text()
    if execution['returncode'] == 0 and not execution['timeout']:
        if (args.engine == 'pdr' and len(re.findall(r'(?m)^Property proved\.',log)) == 1 and
            not re.search(r'\b(error|failed|undecided|disproved|timed out|time limit|was asserted)\b',log,re.I)):
            record['status'] = 'proved_safety_query_only'
        elif 'was asserted' in log:
            record['status'] = 'counterexample_in_query_model'
        elif args.engine == 'bmc':
            match = re.search(r'No output asserted in (\d+) frames\.',log)
            record['reported_no_counterexample_frames'] = int(match[1]) if match else None
            complete = bool(match and int(match[1]) >= args.frames and not re.search(r'resource limit|timeout|undecided',log,re.I))
            record['requested_horizon_completed'] = complete
            record['status'] = 'bounded_only_no_certificate' if complete else 'resource_limited_no_certificate'
    witness = out/'counterexample.aiw'
    record['counterexample_sha256'] = digest(witness) if witness.exists() else None
    try:
        validate_prepared(prepared)
        require(digest(prepared/'summary.json') == summary_hash, 'Preparation record changed during solver run')
        require(digest(Path(__file__)) == script_hash, 'Solver driver changed during run')
    except (ValueError, OSError) as error:
        record.update(status='error', error=str(error))
    (out/'summary.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({'status':record['status'],'accepted_optimization':False}))


if __name__ == '__main__':
    main()
