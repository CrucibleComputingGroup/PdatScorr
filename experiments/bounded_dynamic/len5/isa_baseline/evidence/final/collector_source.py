#!/usr/bin/env python3
"""Collect compact, hash-checked review evidence; never run hardware experiments."""
import argparse
import csv
import hashlib
import json
from pathlib import Path
import shutil

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--build-root', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args(); b, out = args.build_root.resolve(), args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    inventory = []
    def copy(source, relative):
        dest = out/relative; dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, dest)
        assert sha(source) == sha(dest)
        inventory.append({'source': str(source.resolve()), 'copy': str(relative), 'sha256': sha(source), 'bytes': source.stat().st_size})
    def select(name, files):
        for relative in files:
            source = b/name/relative
            if source.exists(): copy(source, Path(name)/relative)
    select('isa_baseline_prepare_v1', ['manifest.json', 'decoder.json', 'isa_operations.sv', 'program_alphabet.sv'])
    select('register_baseline_prepare_v2', ['manifest.json', 'decoder.json', 'program_alphabet.sv'])
    select('register_baseline_prepare_v1', ['decoder.json'])
    for name in ['isa_operations_v2', 'program_alphabet_v1', 'program_registers_v2']:
        select(name, ['summary.json', 'reference.v', 'candidate.v', 'harness.sv', 'run_source.py', 'domain_nonempty.log'])
    for name in ['isa_pair_symbolic_v1', 'alphabet_pair_symbolic_v1', 'register_pair_symbolic_v1']:
        select(name, ['summary.json', 'temporal_source.py', 'recheck_source.py', 'proof/proof.json',
                      'proof/prepare.ys', 'proof/prepare.log', 'proof/aig_export.ys', 'proof/aig_export.log', 'proof/pdr.log'])
    for name in ['isa_domain_symbolic_v4', 'alphabet_domain_symbolic_v4', 'rd_domain_symbolic_v5']:
        select(name, ['summary.json', 'prove_domain_source.py', 'data_path.json', 'harness.sv', 'export.ys', 'base.log', 'induction.log'])
    select('register_lowering_symbolic_v2', ['summary.json', 'reference.json', 'candidate.json', 'reference.v', 'candidate.v',
        'harness.sv', 'lower_demux_source.py', 'prove_lowering_source.py', 'temporal_source.py', 'proof/proof.json',
        'proof/prepare.ys', 'proof/aig_export.ys', 'proof/pdr.log'])
    for name in ['isa_map_original_v1', 'isa_map_operations_v1', 'isa_map_alphabet_v1', 'isa_map_registers_v1']:
        select(name, ['summary.json', 'stat.json', 'map.ys'])
        record = json.loads((b/name/'summary.json').read_text())
        assert sha(b/name/'map.log') == record['execution']['log_sha256']
        assert record['execution']['returncode'] == 0 and not record['execution']['timeout']
    certificates = ['isa_operations_certificate_v3.json', 'program_alphabet_certificate_v3.json', 'program_registers_certificate_v2.json']
    for name in certificates: copy(HERE/'results'/name, Path('certificates')/name)
    copy(b/'pre_fpu_frontend/source/LICENSE', Path('LICENSE.LEN5'))
    copy(Path(__file__), Path('collector_source.py'))
    copy(HERE/'map.py', Path('mapping_source.py'))
    rows = []
    for label, directory, cert in [('Original fixed LEN5', 'isa_map_original_v1', None),
        ('Pscorr ISA operation decoder', 'isa_map_operations_v1', certificates[0]),
        ('Pscorr program-word decoder', 'isa_map_alphabet_v1', certificates[1]),
        ('Pscorr program-word decoder + architectural RF', 'isa_map_registers_v1', certificates[2])]:
        d = json.loads((b/directory/'summary.json').read_text())
        if cert: assert json.loads((HERE/'results'/cert).read_text())['native_candidate_sha256'] == d['design_sha256']
        rows.append({'variant': label, 'cell_area': d['cell_area'], 'cells': d['cells'], 'design_sha256': d['design_sha256'], 'certificate': cert})
    for row in rows: row['reduction_percent'] = 100*(1-row['cell_area']/rows[0]['cell_area'])
    with (out/'comparison.csv').open('w') as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)
    omitted = []
    for directory in sorted({x['copy'].split('/')[0] for x in inventory if '/' in x['copy']}):
        full = b/directory
        if not full.is_dir(): continue
        copied = {str(Path(x['source'])) for x in inventory}
        for f in sorted(full.rglob('*')):
            if f.is_file() and str(f) not in copied:
                omitted.append({'path': str(f), 'sha256': sha(f), 'bytes': f.stat().st_size})
    record = {'status': 'conditionally_certified_native_area_comparison', 'rows': rows,
        'method': 'Pscorr under ISA/program facts; additional timing/microarchitecture increment remains unestablished',
        'original_full_data_root': str(b), 'files': inventory, 'omitted_full_data_files': omitted,
        'omissions': 'Whole-core graphs/netlists, SMT/AIG models, bulk search and map logs retained at original paths with hashes.',
        'no_new_simulation_or_synthesis': True}
    (out/'manifest.json').write_text(json.dumps(record, indent=2)+'\n')
    (out/'SHA256SUMS').write_text(''.join(f'{sha(f)}  {f.relative_to(out)}\n' for f in sorted(out.rglob('*')) if f.is_file()))
    print(json.dumps({'files': sum(f.is_file() for f in out.rglob('*')), 'bytes': sum(f.stat().st_size for f in out.rglob('*') if f.is_file()), 'output': str(out)}))


if __name__ == '__main__':
    main()
