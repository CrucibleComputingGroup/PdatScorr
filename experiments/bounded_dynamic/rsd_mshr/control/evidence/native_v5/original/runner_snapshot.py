#!/usr/bin/env python3
"""Matched constrained ABC correspondence control; formal counts, not cell area.

The one-copy wrapper preserves every hardware input/output and the exact service
monitor. Unknown combinational values become nondeterministic formal inputs;
-zinit preserves unknown FF initialization through additional formal inputs.
Those artifacts prohibit claiming physical hardware area from this AIG.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT))
from odc.temporal import run_command, yosys_path


def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()


def tool_identity(executable, version_args):
    resolved = Path(shutil.which(executable) or executable).resolve()
    version = subprocess.run([str(resolved), *version_args], capture_output=True,
                             text=True, timeout=10)
    return {'path': str(resolved), 'sha256': sha(resolved),
            'version_command': [str(resolved), *version_args],
            'version_returncode': version.returncode,
            'version_output': (version.stdout + version.stderr).strip()}


def header(path):
    with path.open('rb') as f: row=f.readline().decode('ascii').split()
    assert row[0] in ('aig','aag')
    values=list(map(int,row[1:]))+[0]*4
    return dict(zip(('variables','inputs','latches','outputs','ands','bad','constraints','justice','fairness'),values))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    here=Path(__file__).resolve().parent
    parser.add_argument('--baseline',type=Path,default=here.parent/'results/baseline_v5/baseline.json')
    parser.add_argument('--monitor',type=Path,default=here.parent/'ReadServiceContract.sv')
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--spacing',type=int,default=3)
    parser.add_argument('--latency',type=int,default=5)
    parser.add_argument('--depth',type=int,default=6)
    parser.add_argument('--timeout',type=float,default=120)
    parser.add_argument('--yosys',default='/home/allenjin/Projects/DAC_pscorr/tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys')
    parser.add_argument('--abc',default='/usr/bin/yosys-abc')
    args=parser.parse_args()
    if min(args.spacing,args.latency,args.depth)<=0:parser.error('Positive timing/depth required')
    out=args.output.resolve();out.mkdir(parents=True,exist_ok=False)
    if any(c.isspace() or c in ';"\\' for c in str(out)):
        raise ValueError('Control output path must not contain whitespace or command characters')
    baseline=args.baseline.resolve();monitor=args.monitor.resolve()
    design=json.loads(baseline.read_text());module=design['modules']['MshrObserved']
    ports=module['ports'];declarations=[]
    for name,port in ports.items():
        assert re.fullmatch('[A-Za-z_][A-Za-z0-9_]*',name)
        width=len(port['bits']);assert port['direction'] in ('input','output')
        declarations.append(f"    {port['direction']} wire "+(f'[{width-1}:0] ' if width>1 else '')+name)
    wrapper='module PscorrControl(\n'+',\n'.join(declarations)+'\n);\n'
    wrapper+='MshrObserved original('+','.join(f'.{n}({n})' for n in ports)+');\n'
    wrapper+=f'''ReadServiceContract #(.MIN_SPACING({args.spacing}),.MAX_LATENCY({args.latency}),.ORDERED(1)) service(
 .clk(clk),.rst(rst),.read_accept(read_accept),.allocated_id(allocated_id),
 .response_valid(response_valid),.response_id(response_id));
endmodule
'''
    (out/'PscorrControl.sv').write_text(wrapper)
    (out/'ReadServiceContract.sv').write_bytes(monitor.read_bytes())
    (out/'runner_snapshot.py').write_bytes(Path(__file__).read_bytes())
    (out/'temporal_snapshot.py').write_bytes((ROOT/'odc/temporal.py').read_bytes())
    state_bits=sum(len(c['connections'].get('Q',[])) for c in module['cells'].values() if c['type'] in ('$dff','$sdff','$adff','$dffe','$sdffe','$adffe','$ff'))
    report={'status':'running','scope':'Matched formal-AIG correspondence control only; no physical area or RTL equivalence certificate claimed',
            'baseline':str(baseline),'baseline_sha256':sha(baseline),'monitor':str(monitor),'monitor_sha256':sha(monitor),
            'contract':{'min_spacing':args.spacing,'max_latency':args.latency,'ordered':True},
            'functional_input_bits':sum(len(p['bits']) for p in ports.values() if p['direction']=='input'),
            'functional_output_bits':sum(len(p['bits']) for p in ports.values() if p['direction']=='output'),
            'native_ff_bits':state_bits,'top':'PscorrControl','wrapper_sha256':sha(out/'PscorrControl.sv'),
            'initial_state':'Original reset retained; AIGER zinit introduces formal initialization inputs and initial-cycle state. No random-state cycling.',
            'undefined_values':'Nondeterministic extra inputs before first opt and after techmap, with opt -keepdc; not zero constants.',
            'physical_mapping_permitted':False,'stages':{},'variants':{}}
    report['provenance'] = {
        'argv': sys.argv,
        'script_sha256': sha(Path(__file__)),
        'temporal_sha256': sha(ROOT/'odc/temporal.py'),
        'git_head': subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
        'tools': {'yosys': tool_identity(args.yosys, ['-V']),
                  'abc': tool_identity(args.abc, ['-c','version'])}}
    def save(): (out/'summary.json').write_text(json.dumps(report,indent=2)+'\n')
    save()
    normalize=f'''read_json {yosys_path(baseline)}
read_verilog -formal -sv {yosys_path(out/'PscorrControl.sv')} {yosys_path(out/'ReadServiceContract.sv')}
hierarchy -check -top PscorrControl
proc
flatten
setundef -anyseq
opt -keepdc
memory_map
opt -keepdc
chformal -lower
select -assert-min 1 t:$assume
select -assert-none t:$assert
select *
async2sync
techmap
opt -keepdc
simplemap
dfflegalize -cell $_DFF_P_ 01 -mince 99999
clean
setundef -anyseq
delete t:$anyseq
setundef -undriven -expose
aigmap
clean
check -assert
write_aiger -zinit -symbols -map {out/'input.map'} {yosys_path(out/'input.aig')}
'''
    script=out/'prepare.ys';script.write_text(normalize)
    result=run_command([args.yosys,'-Q','-T','-s',str(script)],out/'prepare.log',args.timeout)
    report['stages']['prepare']=result;save()
    if result['timeout'] or result['returncode'] or not (out/'input.aig').exists():
        report['status']='preparation_failed';save();return 1
    initial=header(out/'input.aig');report['formal_input']=initial
    assert initial['outputs']==report['functional_output_bits'] and initial['constraints']>0 and initial['bad']==0
    for name,scorr in [('no_scorr',False),('scorr',True)]:
        folder=out/name;folder.mkdir()
        commands=[f'read_aiger {out/"input.aig"}','strash','print_stats']
        if scorr:commands += [f'scorr -c -m -F {args.depth} -C 30000 -S 20 -v','print_stats',f'write_aiger {folder/"optimized_with_constraints.aig"}']
        commands += ['constr -r -p','rewrite -l','balance -l','print_stats',f'write_aiger {folder/"logic.aig"}']
        abcfile=folder/'run.abc';abcfile.write_text('\n'.join(commands)+'\n')
        result=run_command([args.abc,'-f',str(abcfile)],folder/'abc.log',args.timeout)
        row={'command_result':result,'scorr':scorr,'depth':args.depth,'initial':initial}
        if not result['timeout'] and result['returncode']==0 and (folder/'logic.aig').exists():
            final=header(folder/'logic.aig');row['final']=final;row['aig_sha256']=sha(folder/'logic.aig')
            row['outputs_preserved']=final['outputs']==initial['outputs'] and final['constraints']==0 and final['bad']==0
            row['status']='complete' if row['outputs_preserved'] else 'invalid_output_boundary'
            if final['latches']>state_bits:row['nonhardware_state_lower_bound']=final['latches']-state_bits
        else:row['status']='timeout' if result['timeout'] else 'failed'
        report['variants'][name]=row;save()
    if all(x['status']=='complete' for x in report['variants'].values()):
        base,cut=(report['variants'][v]['final'] for v in ('no_scorr','scorr'))
        report['formal_logic_reduction']={k:{'before':base[k],'after':cut[k], 'difference':base[k]-cut[k],
                                           'fraction':(base[k]-cut[k])/base[k] if base[k] else None} for k in ('ands','latches')}
        report['status']='complete_formal_control'
    else:report['status']='incomplete_control'
    assert sha(baseline)==report['baseline_sha256'] and sha(monitor)==report['monitor_sha256']
    save();print(json.dumps({k:report[k] for k in ('status','contract','variants')},indent=2))
    return 0 if report['status']=='complete_formal_control' else 1

if __name__=='__main__':raise SystemExit(main())
