#!/usr/bin/env python3
"""Collect frozen reset-cube evidence; never run a solver or rewrite models."""
import argparse
import json
from pathlib import Path
import shutil

from reset_cube import digest, read, require

HERE = Path(__file__).resolve().parent


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--native', type=Path, required=True)
    p.add_argument('--tiny', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--fixedpoint', action='store_true')
    args = p.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    files, omitted = [], []
    def collect(source, relative):
        dest = output/relative
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, dest)
        value = digest(source)
        require(digest(dest) == value, 'Evidence copy changed')
        files.append({'source': str(source.resolve()), 'copy': str(relative), 'sha256': value, 'bytes': source.stat().st_size})
    record = read(args.native/'summary.json')
    proof_dependencies = record.get('input_theorem_dependencies_sha256', record.get('dependencies_sha256', {}))
    for path, value in proof_dependencies.items():
        require(digest(Path(path)) == value, 'Native source/theorem dependency changed')
    for root, prefix in ((args.native.resolve(), Path('native')), (args.tiny.resolve(), Path('tiny'))):
        for path in sorted(root.rglob('*')):
            if not path.is_file() or path.is_symlink():
                continue
            relative = prefix/path.relative_to(root)
            if prefix == Path('native') and (path.stat().st_size > 350_000 or path.name in ('source.json', 'projection.json')):
                omitted.append({'source': str(path), 'sha256': digest(path), 'bytes': path.stat().st_size,
                                'reason': 'Large reproducible native model retained in external build'})
            else:
                collect(path, relative)
    test_names = ['test_reset_cube.py'] + (['test_reset_cube_fixedpoint.py'] if args.fixedpoint else [])
    source_names = ['reset_cube.py', 'reset_cube_diagnostic.py', 'collect_reset_cube.py']
    if args.fixedpoint:
        source_names += ['reset_cube_fixedpoint.py']
    for name in source_names:
        collect(HERE/name, Path('sources')/name)
    for name in test_names:
        collect(HERE.parents[3]/'tests/unit'/name, Path('sources')/name)
    for suffix in ('.log', '_execution.json'):
        path = args.tiny.parent/(args.tiny.name+suffix)
        if path.exists():
            collect(path, Path('tiny_execution')/path.name)
    report = {'status': 'source_bound_reset_cube_evidence_collected', 'source_result_status': record['status'],
              'fixedpoint_package': args.fixedpoint, 'accepted_hardware_optimization': False,
              'files': files, 'omitted_external_files': omitted, 'proof_dependencies_sha256': proof_dependencies,
              'no_new_solver_or_export': True}
    (output/'manifest.json').write_text(json.dumps(report, indent=2)+'\n')
    (output/'SHA256SUMS').write_text(''.join(f'{digest(path)}  {path.relative_to(output)}\n'
        for path in sorted(output.rglob('*')) if path.is_file()))
    print(json.dumps({'files': len(files), 'omitted': len(omitted),
                      'bytes': sum(path.stat().st_size for path in output.rglob('*') if path.is_file())}))


if __name__ == '__main__':
    main()
