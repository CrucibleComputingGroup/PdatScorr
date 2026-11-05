#!/usr/bin/env python3
"""Audit and collect derived inactive-FU query facts, without running solvers."""
import argparse
import copy
import json
from pathlib import Path
import shutil

from collect_reset_storage import negative_witness
from inactive_fu_lemmas import BANKS, digest, read, require, slice_reset_ff
from odc.temporal import proof_passed


def audit_query(native,query,summary):
    """Independent whole-graph comparison: only proved Q/FF substitutions."""
    substitutions={int(k):v for k,v in summary['row_reset_substitution']['constant_substitutions'].items()}
    high=summary['native_visible_register_high_substituted']
    require(high not in substitutions,'Native visible selector overlaps bank state')
    substitutions[high]='0'
    require(len(substitutions)==summary['total_proved_reset_state_bits_substituted'],'Substitution bit count differs')
    expected=copy.deepcopy(native);m=expected['modules']['datapath'];removed=[];sliced=[]
    require(not set(substitutions)&{b for p in m['ports'].values() if p['direction']=='input' for b in p['bits']},'Input driver substituted')
    for name,cell in list(m['cells'].items()):
        driven={b for p,d in cell['port_directions'].items() if d=='output' for b in cell['connections'][p]}
        if driven&set(substitutions):
            require('Q' in cell['connections'] and driven==set(cell['connections']['Q']),'Non-FF output substituted')
            q=cell['connections']['Q'];indices=[i for i,b in enumerate(q) if b not in substitutions]
            _,reset=slice_reset_ff(cell,list(range(len(q))))
            require(all(substitutions[b]==reset[i] for i,b in enumerate(q) if b in substitutions),'Replacement is not native reset value')
            if indices:m['cells'][name],_=slice_reset_ff(cell,indices);sliced.append(name)
            else:del m['cells'][name];removed.append(name)
    for cell in m['cells'].values():
        for port,direction in cell['port_directions'].items():
            if direction=='input':cell['connections'][port]=[substitutions.get(b,b) for b in cell['connections'][port]]
    for collection in ('ports','netnames'):
        for value in m[collection].values():value['bits']=[substitutions.get(b,b) for b in value['bits']]
    require(expected==query,'Query graph differs beyond certified reset-state substitutions')
    return {'exact_whole_graph_comparison':True,'reset_bits':len(substitutions),
        'removed_native_ff_cells':removed,'sliced_native_ff_cells':sliced,
        'all_other_cell_functions_ports_parameters_attributes_preserved':True}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--run',required=True,type=Path);p.add_argument('--output',required=True,type=Path)
    p.add_argument('--license',required=True,type=Path)
    args=p.parse_args();source=args.run.resolve();out=args.output.resolve();out.mkdir(parents=True,exist_ok=False)
    summary=read(source/'summary.json')
    require(summary['status']=='program_only_native_reset_facts_composed' and summary['query_only'] and
            not summary['accepted_hardware_optimization'],'Unexpected result scope')
    for path,sha in summary['source_dependency_sha256'].items():require(digest(Path(path))==sha,'Source dependency changed')
    require(digest(source/'native_input.json')==digest(Path(summary['native_input_path']))==summary['native_input_sha256'],'Native source changed')
    require(digest(source/'query_only.json')==summary['query_model_sha256'],'Query model changed')
    audit=audit_query(read(source/'native_input.json'),read(source/'query_only.json'),summary)
    files=[];omitted=[];rows=[]
    def collect(path,relative):
        target=out/relative;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(path,target)
        require(digest(path)==digest(target),'Evidence copy changed')
        files.append({'source':str(path),'copy':str(relative),'sha256':digest(path),'bytes':path.stat().st_size})
    for name in ('summary.json','inactive_fu_lemmas_source.py','replayed_decoder_certificate.json','certificate_replay.log'):
        collect(source/name,Path(name))
    collect(Path(__file__).resolve(),Path('collector_source.py'));collect(args.license.resolve(),Path('LICENSE.LEN5'))
    for bank,prefix in BANKS.items():
        binding=summary['banks'][bank];require(binding['prefix']==prefix,'Bank prefix changed')
        for item in binding['rows']:
            row=item['row'];directory=source/f'{bank}_row_{row}';record=read(directory/'summary.json')
            require(digest(directory/'summary.json')==item['local_summary_sha256'],'Local proof summary changed')
            require(record['projection']['prefix']==prefix and record['projection']['row']==row,'Row proof binding changed')
            require(record['admission_during_reset_restricted'] is False,'Reset-time admission constrained')
            for path,sha in record['dependencies_sha256'].items():require(digest(Path(path))==sha,'Local artifact changed')
            positive,negative=record['proofs']['positive'],record['proofs']['negative']
            require(proof_passed(positive['base']) and proof_passed(positive['induction']) and '-i' in positive['induction']['argv'],'Missing unbounded proof')
            require(negative['counterexample_found'],'Local negative control missing')
            for side,result in [('positive',positive),('negative',negative)]:
                require(digest(directory/side/'model.smt2')==result['model_sha256'] and
                        digest(directory/side/'lowered.json')==result['lowered_sha256'],'Proof model changed')
            witness=negative_witness(directory/'negative/counterexample.vcd',row)
            for name in ['summary.json','projection.json','positive/harness.sv','positive/export.ys',
                'positive/base.log','positive/induction.log','negative/harness.sv','negative/export.ys',
                'negative/base.log','negative/counterexample.vcd']:
                collect(directory/name,Path(directory.name)/name)
            rows.append({'bank':bank,'prefix':prefix,'row':row,'ff_bits':record['projection']['ff_bits'],
                'combinational_cells':len(record['projection']['combinational_cells']),
                'arbitrary_other_ff_q_bits':len(record['projection']['arbitrary_other_ff_q_bits']),
                'negative_witness':witness})
    for directory in ('register_replay','dispatch_replay','decoder_replay'):
        for path in sorted((source/directory).iterdir()):
            if path.suffix in ('.log','.ys') or path.name=='lowered.json':collect(path,Path(directory)/path.name)
    copied={x['source'] for x in files}
    for path in sorted(source.rglob('*')):
        if path.is_file() and str(path) not in copied:
            omitted.append({'source':str(path),'sha256':digest(path),'bytes':path.stat().st_size})
    report={'status':'native_reset_facts_and_query_substitution_audited','source_run':str(source),
        'query_only':True,'accepted_hardware_optimization':False,'no_physical_area_claim':True,
        'no_new_environment_or_timing_premises':True,'local_no_admission_premises_discharged_by_native_zero_issue_valid':True,
        'graph_audit':audit,'rows':rows,'files':files,'omitted_external_files':omitted,
        'limitations':'Initial reset and exact external program-word domain remain required. Local relaxed-premise counterexamples are cut-boundary traces, not feasible whole-core executions under the derived zero-issue-valid theorem. Generic row patch records remain conditional in isolation; the surrounding source-bound EU/insert chain discharges them only for these MUL/DIV banks. Hardware export remains unchanged; this artifact is for proof-query simplification only.'}
    (out/'manifest.json').write_text(json.dumps(report,indent=2)+'\n')
    (out/'SHA256SUMS').write_text(''.join(f'{digest(f)}  {f.relative_to(out)}\n' for f in sorted(out.rglob('*')) if f.is_file()))
    print(json.dumps({'files':sum(f.is_file() for f in out.rglob('*')),'bytes':sum(f.stat().st_size for f in out.rglob('*') if f.is_file()),'rows':len(rows),'bits':audit['reset_bits']}))


if __name__=='__main__':main()
