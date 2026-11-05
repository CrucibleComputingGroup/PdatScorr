#!/usr/bin/env python3
"""Audit retained word-level export; no solver invocation."""
import hashlib
import json
from pathlib import Path
import re

HERE=Path(__file__).resolve().parent
RAW=Path('/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build/word_solver_alu_mul_v1')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    record=json.loads((RAW/'summary.json').read_text());target=RAW/'target'
    assert sha(target/'exported.json')==record['target_export']['exported_json_sha256']
    assert sha(target/'model.btor2')==record['target_export']['btor_sha256']
    assert sha(target/'export.log')==record['target_export']['export']['log_sha256']
    m=json.loads((target/'exported.json').read_text())['modules']['AdmissionScreen']
    used={bit for cell in m['cells'].values() for pin,bits in cell['connections'].items()
        if cell['port_directions'][pin]=='input' for bit in bits if type(bit)is int}
    outputs={bit for port in m['ports'].values() if port['direction']=='output'
        for bit in port['bits'] if type(bit)is int}
    aliases=[]
    warnings=[line for line in (target/'export.log').read_text().splitlines() if line.startswith('Warning:')]
    for line in warnings:
        match=re.fullmatch(r'Warning: No driver for signal \\(.*) \[(\d+)(?::(\d+))?\]\.',line)
        assert match,line
        name,high,low=match.groups();high=int(high);low=int(low or high)
        net=m['netnames'][name];assert not net.get('upto',0)
        offset=net.get('offset',0);bits=net['bits'][low-offset:high-offset+1]
        assert len(bits)==high-low+1 and not set(bits)&(used|outputs)
        aliases.append({'name':name,'high':high,'low':low,'bits':bits,
            'functional_cell_input_overlap':[],'top_output_overlap':[]})
    widths={kind:sum(len(cell['connections'].get('Q',cell['connections'].get('Y',[])))
        for cell in m['cells'].values() if cell['type']==kind) for kind in ('$ff','$anyseq','$initstate')}
    btor=record['target_export']['btor']
    assert btor['state_bits']==sum(widths.values()) and len(btor['initializers'])==1
    assert not any('init' in net.get('attributes',{}) for net in m['netnames'].values())
    result={'status':'export_structure_and_unused_aliases_audited','new_solver_queries':0,
        'prepared_source_sha256':record['target_export']['source_sha256'],
        'exported_json_sha256':sha(target/'exported.json'),'btor_sha256':sha(target/'model.btor2'),
        'export_log_sha256':sha(target/'export.log'),'audit_sha256':sha(Path(__file__)),
        'semantic_properties':record['target_export']['property_counts'],
        'btor_bad_conditions':btor['bad'],'btor_constraints':btor['constraint'],
        'word_level_nodes':sum(btor['operators'].values()),'source_state_and_symbolic_widths':widths,
        'btor_state_bits':btor['state_bits'],'btor_inputs':btor['input_bits'],
        'explicit_native_state_init_attributes':0,'only_btor_initializer':'Original $initstate bookkeeping flag, initially one',
        'undriven_alias_ranges':aliases,'all_warned_alias_bits_functionally_unused':True,
        'warned_bit_occurrences':sum(len(row['bits']) for row in aliases)}
    (HERE/'export_audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({key:result[key] for key in ('status','word_level_nodes','source_state_and_symbolic_widths','warned_bit_occurrences')}))

if __name__=='__main__':main()
