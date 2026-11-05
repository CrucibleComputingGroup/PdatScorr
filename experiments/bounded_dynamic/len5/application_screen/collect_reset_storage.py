#!/usr/bin/env python3
"""Hash-check and collect conditional row proofs; never run a hardware query."""
import argparse
import json
from pathlib import Path
import shutil

from reset_storage import digest, proof_passed, require


def read(path):
    return json.loads(path.read_text())


def negative_witness(path, row):
    """Read complete SMT frames, avoiding trailing partial clock-only frames."""
    scope=[];wanted={};frames=[];block={};step=None
    fields={'insert_i','new_index_i','row_q','rst_ni'}
    def finish():
        if step is not None and fields<=set(block):frames.append({'step':step,**block})
    for line in path.read_text().splitlines():
        words=line.split()
        if line.startswith('$scope'):scope.append(words[2])
        elif line.startswith('$upscope'):scope.pop()
        elif line.startswith('$var'):
            if scope==['ResetStorageProof'] and words[4] in fields:wanted[words[3]]=words[4]
        elif line.startswith('#'):
            finish();block={};step=None
        elif line.startswith('b'):
            value,key=words;value=value[1:]
            if key=='t':step=int(value,2)
            elif key in wanted:
                require(set(value)<={'0','1'},'Undefined value in selected counterexample observation')
                block[wanted[key]]=int(value,2)
    finish()
    require(frames and frames[0]['rst_ni']==0 and frames[0]['row_q']==0,'Counterexample lacks native reset base')
    for old,new in zip(frames,frames[1:]):
        if old['rst_ni']==1 and old['insert_i']==1 and old['new_index_i']==row and new['row_q']!=0:
            return {'admission_step':old['step'],'failure_step':new['step'], 'admitted_numeric_row':row,
                    'nonzero_row_value_hex':hex(new['row_q']), 'scope':'Component cut-boundary witness only; not a whole-core allocator trace'}
    raise ValueError('Negative trace does not exhibit admission followed by nonreset selected row')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run',type=Path,required=True);parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--license',type=Path,required=True)
    args=parser.parse_args();source=args.run.resolve();out=args.output.resolve();out.mkdir(parents=True,exist_ok=False)
    summary=read(source/'summary.json')
    require(summary['status']=='all_conditional_local_theorems_proved' and not summary['accepted_optimization'], 'Incomplete/accepted source family')
    for path,sha in summary['source_sha256'].items():require(digest(Path(path))==sha,'Source changed since local theorem')
    files=[];omitted=[];rows=[]
    def copy(path,relative):
        target=out/relative;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(path,target)
        require(digest(path)==digest(target),'Copied evidence changed')
        files.append({'source':str(path),'copy':str(relative),'sha256':digest(path),'bytes':path.stat().st_size})
    for name in ('summary.json','reset_storage_source.py','arith_rs_source.sv'):copy(source/name,Path(name))
    copy(args.license.resolve(),Path('LICENSE.LEN5'));copy(Path(__file__).resolve(),Path('collector_source.py'))
    for item in summary['rows']:
        row=item['row'];directory=source/f'row_{row}';record=read(directory/'summary.json')
        require(record['status']=='conditional_reset_storage_proved' and record['admission_during_reset_restricted'] is False,
                'Final theorem must permit arbitrary reset-time admission')
        for path,sha in record['dependencies_sha256'].items():require(digest(Path(path))==sha,'Proof artifact changed')
        positive,negative=record['proofs']['positive'],record['proofs']['negative']
        require(proof_passed(positive['base']) and proof_passed(positive['induction']) and '-i' in positive['induction']['argv'], 'Unbounded theorem missing')
        require(negative['counterexample_found'],'Negative control missing')
        for side,result in [('positive',positive),('negative',negative)]:
            require(digest(directory/side/'model.smt2')==result['model_sha256'],'SMT model changed')
            require(digest(directory/side/'lowered.json')==result['lowered_sha256'],'Lowered model changed')
        witness=negative_witness(directory/'negative/counterexample.vcd',row)
        patch=read(directory/'conditional_patch.json')
        require(patch['status']=='conditional_proposal_only' and not patch['accepted_optimization'] and
                not patch['global_premise_discharged'] and patch['required_no_admission_rows']==[row], 'Patch status/scope changed')
        require(patch['reset_constant_bits']==record['projection']['ff_bits'],'Patch selected-bit count changed')
        names=['summary.json','projection.json','conditional_patch.json','positive/harness.sv','positive/export.ys',
               'positive/base.log','positive/induction.log','negative/harness.sv','negative/export.ys','negative/base.log','negative/counterexample.vcd']
        for name in names:copy(directory/name,Path(f'row_{row}')/name)
        copied={str((directory/name).resolve()) for name in names}
        for path in sorted(directory.rglob('*')):
            if path.is_file() and str(path.resolve()) not in copied:
                omitted.append({'source':str(path),'sha256':digest(path),'bytes':path.stat().st_size})
        rows.append({'row':row,'raw_selected_ff_bits':record['projection']['ff_bits'],
                     'selected_native_ff_cells':len(record['projection']['selected_ff_slices']),
                     'preserved_combinational_cells':len(record['projection']['combinational_cells']),
                     'arbitrary_other_ff_q_bits':len(record['projection']['arbitrary_other_ff_q_bits']),
                     'negative_witness':witness})
    report={'status':'eight_conditional_native_reset_theorems_collected','accepted_optimization':False,
            'global_premise_discharged':False,'no_area_or_whole_core_saving_claim':True,
            'local_premise':'Initial native reset and rst_ni -> !(actual insert && actual new_idx == row)',
            'proof_method':'Exact native row FF/reset slices and combinational fanin; other FF-Q and native RS input boundaries are arbitrary',
            'source_run':str(source),'rows':rows,'files':files,'omitted_external_files':omitted,
            'limitations':'Local negative traces are cut-boundary component traces. A global admission proof is still required before any rewrite acceptance. Full-core proposals and mapping are not emitted.'}
    (out/'manifest.json').write_text(json.dumps(report,indent=2)+'\n')
    (out/'SHA256SUMS').write_text(''.join(f'{digest(p)}  {p.relative_to(out)}\n' for p in sorted(out.rglob('*')) if p.is_file()))
    print(json.dumps({'files':sum(p.is_file() for p in out.rglob('*')),
                      'bytes':sum(p.stat().st_size for p in out.rglob('*') if p.is_file()),'rows':len(rows)}))


if __name__=='__main__':main()
