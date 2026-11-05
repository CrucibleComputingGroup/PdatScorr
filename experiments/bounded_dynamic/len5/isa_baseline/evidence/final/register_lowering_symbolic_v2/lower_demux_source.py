"""Expose every native demultiplexer arm without specializing its behavior."""
import copy

from odc.temporal import parameter_int


def expand_demuxes(design, top, selected_cells):
    result = copy.deepcopy(design)
    module = result['modules'][top]
    bits = [bit for cell in module['cells'].values() for port in cell['connections'].values()
            for bit in port if isinstance(bit, int)]
    bits += [bit for net in [*module['ports'].values(), *module['netnames'].values()]
             for bit in net['bits'] if isinstance(bit, int)]
    next_bit = max(bits)+1
    changes = []
    for serial, name in enumerate(sorted(selected_cells)):
        original = module['cells'][name]
        if original['type'] != '$demux':
            continue
        width = parameter_int(original['parameters']['WIDTH'])
        selector_width = parameter_int(original['parameters']['S_WIDTH'])
        con = original['connections']
        assert width > 0 and selector_width > 0
        assert len(con['A']) == width and len(con['S']) == selector_width
        assert len(con['Y']) == width*(1 << selector_width)
        assert all(isinstance(bit, int) for bit in con['Y'])
        del module['cells'][name]
        generated = []
        for index in range(1 << selector_width):
            selected = [next_bit]; next_bit += 1
            prefix = f'$pscorr_demux_{serial}_{index}'
            for suffix in ('_eq', '_mux'):
                assert prefix+suffix not in module['cells']
            metadata = copy.deepcopy(original.get('attributes', {}))
            metadata['pscorr_unconditional_demux_lowering'] = 1
            module['cells'][prefix+'_eq'] = {'hide_name': 1, 'type': '$eq', 'attributes': metadata,
                'parameters': {'A_SIGNED': 0, 'B_SIGNED': 0, 'A_WIDTH': selector_width,
                               'B_WIDTH': selector_width, 'Y_WIDTH': 1},
                'port_directions': {'A': 'input', 'B': 'input', 'Y': 'output'},
                'connections': {'A': list(con['S']), 'B': list(format(index, f'0{selector_width}b')[::-1]), 'Y': selected}}
            module['cells'][prefix+'_mux'] = {'hide_name': 1, 'type': '$mux', 'attributes': metadata,
                'parameters': {'WIDTH': width}, 'port_directions': {'A': 'input', 'B': 'input', 'S': 'input', 'Y': 'output'},
                'connections': {'A': ['0']*width, 'B': list(con['A']), 'S': selected,
                                'Y': list(con['Y'][index*width:(index+1)*width])}}
            generated += [prefix+'_eq', prefix+'_mux']
        changes.append({'original_cell': name, 'data_width': width, 'selector_width': selector_width,
                        'generated_cells': generated, 'arms_removed': 0})
    return result, changes
