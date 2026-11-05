#!/usr/bin/env python3
"""Check the exact native RF demux expansion unconditionally on all inputs."""
import argparse
import copy
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[3]))
sys.path.insert(0, str(HERE.parent))
from odc.temporal import digest, export_design, prove_pair
import odc.temporal as temporal_backend
from prepare_frontend import workspace_root
from lower_demux import expand_demuxes


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--original-rf', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--yosys', default=str(workspace_root(HERE)/'tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys'))
    args = parser.parse_args()
    out = args.output.resolve(); out.mkdir(parents=True, exist_ok=False)
    (out/'temporal_source.py').write_bytes(Path(temporal_backend.__file__).read_bytes())
    (out/'prove_lowering_source.py').write_bytes(Path(__file__).read_bytes())
    (out/'lower_demux_source.py').write_bytes((HERE/'lower_demux.py').read_bytes())
    source = json.loads(args.original_rf.read_text())['modules']['DecoderBase']
    cells = {name: cell for name, cell in source['cells'].items() if cell['type'] == '$demux'}
    assert len(cells) == 1
    name, cell = next(iter(cells.items()))
    ports = {pin: {'direction': cell['port_directions'][pin], 'bits': bits} for pin, bits in cell['connections'].items()}
    model = {'modules': {'DemuxReference': {'attributes': {'top': '1'}, 'ports': ports,
        'netnames': {pin: {'hide_name': 0, 'attributes': {}, 'bits': port['bits']} for pin, port in ports.items()},
        'cells': {name: copy.deepcopy(cell)}}}}
    changed, transformations = expand_demuxes(model, 'DemuxReference', [name])
    (out/'reference.json').write_text(json.dumps(model)+'\n')
    (out/'candidate.json').write_text(json.dumps(changed)+'\n')
    reference, candidate = out/'reference.v', out/'candidate.v'
    export_design(model, 'DemuxReference', 'DemuxReference', reference, args.yosys, 30)
    export_design(changed, 'DemuxReference', 'DemuxCandidate', candidate, args.yosys, 30)
    widths = {pin: len(port['bits']) for pin, port in ports.items()}
    harness = out/'harness.sv'
    harness.write_text(f'''module TemporalMiter(input [{widths['A']-1}:0] A,input [{widths['S']-1}:0] S);
      wire [{widths['Y']-1}:0] a,b;
      DemuxReference reference(.A(A),.S(S),.Y(a));
      DemuxCandidate candidate(.A(A),.S(S),.Y(b));
      always @* assert(a==b);
    endmodule\n''')
    result = prove_pair(reference, candidate, harness, 'TemporalMiter', out/'proof', yosys=args.yosys,
        smtbmc=str(Path(args.yosys).with_name('yosys-smtbmc')), solver='z3', depth=2, timeout=60,
        engine='pdr', abc='/usr/local/bin/abc', assert_state_correspondence=False)
    record = {'status': 'proved' if result['proven'] else 'unproved', 'scope': 'Unconditional exact native demux expansion; zero specialization premises',
              'proof': result, 'native_widths': widths, 'transformations': transformations,
              'original_rf_sha256': digest(args.original_rf), 'lowering_source_sha256': digest(HERE/'lower_demux.py')}
    (out/'summary.json').write_text(json.dumps(record, indent=2)+'\n')
    print(json.dumps({'status': record['status'], 'widths': widths}))
    return 0 if result['proven'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
