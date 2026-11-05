#!/usr/bin/env python3
"""Map one native fixed-capacity core; formal monitors are forbidden."""
import argparse
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[3]))
sys.path.insert(0, str(HERE.parent))
from odc.temporal import checked_yosys, digest, yosys_path
from prepare_frontend import workspace_root


def main():
    workspace = workspace_root(HERE)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--design', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--yosys', default=str(workspace/'tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys'))
    parser.add_argument('--liberty', type=Path, default=Path('/opt/pdk/skywater-pdk/libraries/sky130_fd_sc_hd/latest/timing/sky130_fd_sc_hd__tt_025C_1v80.lib'))
    args = parser.parse_args()
    out = args.output.resolve(); out.mkdir(parents=True, exist_ok=False)
    record = {'status': 'running', 'scope': 'Native cell-area estimate; domain-conditional decoder specialization, no layout/timing claim',
              'design_sha256': digest(args.design), 'liberty_sha256': digest(args.liberty), 'script_sha256': digest(Path(__file__))}
    (out/'summary.json').write_text(json.dumps(record, indent=2)+'\n')
    try:
        record['execution'] = checked_yosys(args.yosys,
            f'read_json {yosys_path(args.design)}\nhierarchy -check -top datapath\ncheck -assert\n'
            'select -assert-none t:$assume t:$assert t:$cover t:$check t:$anyseq t:$anyconst\nselect *\n'
            'bwmuxmap\nbmuxmap\ndemuxmap\nmemory_map\nsynth -top datapath\n'
            f'dfflibmap -liberty {yosys_path(args.liberty)}\nabc -liberty {yosys_path(args.liberty)}\nclean\n'
            f'tee -o {yosys_path(out/"stat.json")} stat -json -liberty {yosys_path(args.liberty)}\n', out, 'map', 600)
        stats = json.loads((out/'stat.json').read_text())['modules']['\\datapath']
        assert not any(name.startswith('$') for name in stats['num_cells_by_type'])
        record.update(status='mapped', cell_area=stats['area'], cells=stats['num_cells'], cell_types=stats['num_cells_by_type'])
    except (AssertionError, RuntimeError, OSError, ValueError, KeyError) as error:
        record.update(status='failed', error=str(error))
    assert digest(args.design) == record['design_sha256'] and digest(args.liberty) == record['liberty_sha256']
    (out/'summary.json').write_text(json.dumps(record, indent=2)+'\n')
    print(json.dumps({key: value for key, value in record.items() if key not in ('cell_types', 'execution')}))
    return 0 if record['status'] == 'mapped' else 1


if __name__ == '__main__':
    raise SystemExit(main())
