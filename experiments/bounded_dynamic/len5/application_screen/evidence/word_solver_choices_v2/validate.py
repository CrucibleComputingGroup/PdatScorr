#!/usr/bin/env python3
"""Supplemental paired check: anyseq may vary; anyconst must stay fixed."""
import argparse
import importlib.util
import json
from pathlib import Path
import shutil

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--repo',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    app=args.repo/'experiments/bounded_dynamic/len5/application_screen'
    spec=importlib.util.spec_from_file_location('word_solver',app/'word_solver.py')
    helper=importlib.util.module_from_spec(spec);spec.loader.exec_module(helper)
    helper_hash=helper.digest(app/'word_solver.py')
    helper.TINY={'value_must_vary_negative':('counterexample_in_query_model', '''module Tiny(input clk);
(* anyseq *) reg [3:0] value;
reg [3:0] previous;
reg sampled = 0;
always @(posedge clk) begin previous <= value; sampled <= 1; end
always @* if(sampled) assert(value == previous);
endmodule
''')}
    helper.TINY['value_anyconst_positive']=('proved_safety_query_only', helper.TINY['value_must_vary_negative'][1].replace('(* anyseq *)', '(* anyconst *)'))
    out=args.output.resolve();out.mkdir(parents=True,exist_ok=False)
    records=helper.validate_tiny(out,str(helper.OSS/'yosys'),str(helper.OSS/'pono'))
    assert helper.digest(app/'word_solver.py')==helper_hash
    model=(out/'value_must_vary_negative/model.btor2').read_text()
    rows=[line.split(';',1)[0].split() for line in model.splitlines()]
    rows=[row for row in rows if row]
    states=[row[0] for row in rows if row[1]=='state']
    next_states={row[3] for row in rows if row[1]=='next'}
    free=[i for i,state in enumerate(states) if state not in next_states]
    assert len(free)==1
    values=[];frame=None;in_state=False
    for line in (out/'value_must_vary_negative/counterexample.wit').read_text().splitlines():
        if line.startswith('#'):frame=int(line[1:]);in_state=True
        elif line.startswith('@'):in_state=False
        elif in_state and line.split() and line.split()[0]==str(free[0]):
            values.append({'frame':frame,'bits':line.split()[1]})
    assert len(values)>=2 and values[0]['bits']!=values[1]['bits']
    result={'status':'paired_anyseq_anyconst_semantics_validated','anyseq_values':values,'target_query_rerun':False,
        'scope':'Tiny Pono MBIC3 detects varying symbolic value; BMC witness independently checked by btorsim',
        'helper_sha256':helper_hash,'driver_sha256':helper.digest(Path(__file__)),'records':records}
    (out/'summary.json').write_text(json.dumps(result,indent=2)+'\n')
    evidence=Path(__file__).resolve().parent
    for path in out.rglob('*'):
        if path.is_file():
            dest=evidence/path.relative_to(out);dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(path,dest)
    (evidence/'SHA256SUMS').write_text(''.join(f'{helper.digest(path)}  {path.relative_to(evidence)}\n'
        for path in sorted(evidence.rglob('*')) if path.is_file() and path.name!='SHA256SUMS'))
    print(result['status'])

if __name__=='__main__':main()
