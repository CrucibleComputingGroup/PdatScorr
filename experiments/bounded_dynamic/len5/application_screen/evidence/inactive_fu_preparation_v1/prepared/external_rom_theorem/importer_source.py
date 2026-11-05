"""Validate the external ROM theorem before importing native word lemmas.

This performs a small model-export replay, never a new solver query. The exact
producer text and every core port must match the proved arbitrary-core model.
"""
from __future__ import annotations
import json
import os
from pathlib import Path
import sys

import odc.temporal as temporal
from odc.temporal import checked_yosys, digest, formal_lower_command, formal_prepare_command, proof_passed, yosys_path
import rom_domain


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read(path):
    return json.loads(Path(path).read_text())


def verify_dependencies(record):
    for name, expected in record['proof_dependencies_sha256'].items():
        require(digest(Path(name)) == expected, 'External ROM theorem dependency changed: '+name)


def validate_rom_domain(certificate, harness, core, image, directory, *, allowed_words, yosys, timeout=30):
    """Bind an unbounded producer theorem to this exact generated native harness."""
    require(sys.flags.optimize == 0 and os.environ.get('PYTHONOPTIMIZE', '') in ('', '0'),
            'ROM theorem validation requires Python assertion checks enabled')
    certificate, harness, core = map(lambda p: Path(p).resolve(), (certificate, harness, core))
    directory = Path(directory).resolve(); directory.mkdir()
    info = read(certificate); evidence = certificate.parent
    require(info['status'] == 'proved_with_two_failing_negative_controls', 'External ROM theorem is not proved')
    require(info['source_harness_sha256'] == digest(harness), 'Exact producer harness changed')
    require(info['rom_image_sha256'] == image['image_sha256'] == digest(evidence/'program.hex'), 'ROM image changed')
    require(info['core_port_descriptor_sha256'] == digest(core), 'Native core descriptor changed')
    require(digest(evidence/'core_ports.json') == info['core_ports_sha256'], 'Proved core port descriptor changed')
    ports = read(core)['modules']['datapath']['ports']
    require(ports == read(evidence/'core_ports.json'), 'Core output cut boundary changed')
    require(info['domain_words'] == [f'{x:08x}' for x in sorted(set(image['words'].values()) | {0})],
            'ROM theorem concludes a different word domain')
    require(set(int(word, 16) for word in info['domain_words']) <= set(allowed_words),
            'External ROM theorem does not imply the native word premise')
    require(digest(Path(rom_domain.__file__)) == info['runner_sha256'] == digest(evidence/'rom_domain.py'),
            'ROM producer extractor source changed')
    require(digest(Path(temporal.__file__)) == info['safe_formal_backend_sha256'] == digest(evidence/'temporal_source.py'),
            'ROM theorem formal frontend source changed')
    positive = info['variants'][0]
    require(positive['name'] == 'positive' and positive['status'] == 'proved_unbounded', 'Missing positive unbounded theorem')
    require(positive['property_counts'] == {'assert': 3, 'assume': 1, 'cover': 0}, 'Unexpected ROM theorem properties')
    # Reconstruct the checker from this very harness, retaining all producer
    # transitions while exposing every native core output as a free input.
    checker, extraction = rom_domain.extract_producer(harness.read_text(), ports, image['words'].values(), helpers=True)
    require(checker == (evidence/'positive/RomDomain.sv').read_text() and extraction == positive['extraction'],
            'ROM theorem changed the native producer or its cut boundary')
    expected_files = {'source_harness.sv': 'source_harness_sha256', 'RomDomain.sv': 'checker_sha256',
                      'model.json': 'model_json_sha256', 'model.smt2': 'smt_sha256'}
    dependencies = {str(p): digest(p) for p in (certificate, harness, core, Path(__file__).resolve(),
        Path(rom_domain.__file__).resolve(), Path(temporal.__file__).resolve(), evidence/'program.hex',
        evidence/'core_ports.json', evidence/'rom_domain.py', evidence/'temporal_source.py')}
    for name, field in expected_files.items():
        path = evidence/'positive'/name
        require(digest(path) == positive[field], 'External ROM proof artifact changed: '+name)
        dependencies[str(path)] = digest(path)
    original = Path(positive['prepare']['argv'][-1]).resolve().parent
    for name, field in expected_files.items():
        path = original/name
        require(digest(path) == positive[field], 'Original ROM proof artifact changed: '+name)
        dependencies[str(path)] = digest(path)
    for mode in ('base', 'induction'):
        execution = positive[mode]
        require(proof_passed(execution), 'ROM theorem did not pass '+mode)
        command = [execution['argv'][0], '-s', 'z3', '-t', '6', '--noprogress']
        command += ['-i'] if mode == 'induction' else ['--dump-vcd', str(original/'counterexample.vcd')]
        command += [str(original/'model.smt2')]
        require(execution['argv'] == command, 'ROM solver checked a different obligation')
        log = Path(execution['log'])
        require(digest(log) == execution['log_sha256'] == digest(evidence/'positive'/f'{mode}.log'),
                'ROM theorem solver log changed')
        if mode == 'induction':
            require('Temporal induction successful.' in log.read_text(), 'Missing unbounded ROM induction result')
        dependencies[str(log)] = digest(log)
    model = read(evidence/'positive/model.json')['modules']['RomDomain']
    counts = {kind: sum(c['type'] == '$'+kind for c in model['cells'].values()) for kind in ('assert', 'assume', 'cover')}
    require(counts == positive['property_counts'], 'ROM model property count changed')
    require(not any('init' in net.get('attributes', {}) for net in model['netnames'].values()), 'ROM pipeline was initialized')
    require(not any(bit in ('x', 'z') for cell in model['cells'].values() for bits in cell['connections'].values() for bit in bits),
            'ROM model contains literal undefined choices')
    before = (f'read_verilog -formal -sv {yosys_path(original/"RomDomain.sv")}\n'+formal_prepare_command('RomDomain')+
              formal_lower_command(yosys)+'async2sync\ndffunmap\nsetundef -anyseq\n')
    after = (f'write_json {yosys_path(original/"model.json")}\nwrite_smt2 -wires {yosys_path(original/"model.smt2")}\n')
    script = (evidence/'positive/prepare.ys').read_text()
    require(script == before+after == (original/'prepare.ys').read_text(), 'ROM theorem export pipeline changed')
    dependencies[str(evidence/'positive/prepare.ys')] = digest(evidence/'positive/prepare.ys')
    dependencies[str(original/'prepare.ys')] = digest(original/'prepare.ys')
    replay = checked_yosys(yosys, before+f'write_json {yosys_path(directory/"model.json")}\n'+
        f'write_smt2 -wires {yosys_path(directory/"model.smt2")}\n', directory, 'replay', timeout)
    require(read(directory/'model.json') == read(original/'model.json'), 'Replayed ROM model JSON differs')
    require(digest(directory/'model.smt2') == positive['smt_sha256'], 'Replayed ROM SMT differs')
    record = {'status': 'exact_external_rom_domain_certified', 'assumptions_added': 0,
        'conclusion': '(rst_ni && instr_rvalid_i) -> word in exact ROM alphabet or zero',
        'arbitrary_core_output_ports': extraction['arbitrary_core_output_ports'],
        'initial_pipeline_state': extraction['initial_pipeline_state'], 'domain_words': info['domain_words'],
        'certificate_sha256': digest(certificate), 'certificate_path': str(certificate),
        'model_properties': counts, 'model_export_replay': replay, 'proof_dependencies_sha256': dependencies}
    verify_dependencies(record)
    (directory/'importer_source.py').write_bytes(Path(__file__).read_bytes())
    (directory/'certificate.json').write_bytes(certificate.read_bytes())
    (directory/'summary.json').write_text(json.dumps(record, indent=2)+'\n')
    return record
