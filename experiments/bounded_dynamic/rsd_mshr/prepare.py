#!/usr/bin/env python3
"""Copy pinned original RSD dependencies and export a small unmodified component."""
import argparse, hashlib, json, shutil, subprocess, time
from pathlib import Path

HERE=Path(__file__).resolve().parent
REVISION='7b65f6ba0bce58d4d859082660123b7100aae975'
SOURCES='''MicroArchConf.sv
BasicTypes.sv
Memory/MemoryMapTypes.sv
RenameLogic/ActiveListIndexTypes.sv
Cache/CacheSystemTypes.sv
Memory/MemoryTypes.sv
Decoder/OpFormat.sv
Decoder/MicroOp.sv
RegisterFile/BypassTypes.sv
FetchUnit/FetchUnitTypes.sv
FloatingPointUnit/FPUTypes.sv
LoadStoreUnit/LoadStoreUnitTypes.sv
RenameLogic/RenameLogicTypes.sv
Scheduler/SchedulerTypes.sv
Pipeline/PipelineTypes.sv
IO/IO_UnitTypes.sv
Privileged/CSR_UnitTypes.sv
Debug/DebugTypes.sv
LoadStoreUnit/LoadStoreUnitIF.sv
Recovery/RecoveryManagerIF.sv
ControllerIF.sv
Cache/DCacheIF.sv
Cache/CacheSystemIF.sv
Primitives/Queue.sv
Primitives/RAM.sv
Primitives/Picker.sv
Primitives/FreeList.sv
Cache/DCache.sv
Cache/MemoryAccessController.sv'''.splitlines()
DEFINES=['RSD_SYNTHESIS','RSD_SYNTHESIS_DESIGN_COMPILER','REF=input',
         'RSD_DISABLE_DEBUG_REGISTER','RSD_DISABLE_PERFORMANCE_COUNTER',
         'RSD_MARCH_INT_ISSUE_WIDTH=2','RSD_MARCH_FP_PIPE','RSD_ENABLE_ZBA','RSD_ENABLE_ZICOND']

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('output',type=Path)
    p.add_argument('--rsd',type=Path,required=True)
    p.add_argument('--yosys',type=Path,required=True)
    args=p.parse_args()
    out=args.output.resolve(); rsd=args.rsd.resolve(); src=rsd/'Processor/Src'
    if out.exists():raise SystemExit('Refusing existing output directory')
    revision=subprocess.check_output(['git','-C',str(rsd),'rev-parse','HEAD'],text=True).strip()
    if revision!=REVISION:raise SystemExit('Unexpected RSD revision '+revision)
    out.mkdir(parents=True)
    hashes={}
    for relative in SOURCES+['BasicMacros.sv','SysDeps/XilinxMacros.vh']:
        file=src/relative
        # Verify original tracked bytes, not just the checkout HEAD.
        original=subprocess.check_output(['git','-C',str(rsd),'show',REVISION+':Processor/Src/'+relative])
        if file.read_bytes()!=original:raise SystemExit('Modified source: '+relative)
        target=out/'src'/relative;target.parent.mkdir(parents=True,exist_ok=True)
        target.write_bytes(original);hashes[relative]=sha(target)
    shutil.copy2(HERE/'MshrObserved.sv',out/'MshrObserved.sv')
    command=' '.join(['read_slang','--single-unit','--top','MshrObserved','--no-implicit-memories',
                      '-I'+str(out/'src'),*['-D'+s for s in DEFINES],
                      *[str(out/'src'/s) for s in SOURCES],str(out/'MshrObserved.sv')])
    script=out/'baseline.ys'
    script.write_text(command+'\nprep -top MshrObserved -flatten\nmemory_map\nopt_clean\ncheck\n'
        +'write_json '+str(out/'baseline.json')+'\nwrite_verilog -noattr '+str(out/'baseline.v')+'\n'
        +'stat\n')
    manifest={'status':'prepared','rsd_revision':revision,'source_sha256':hashes,
        'wrapper_sha256':sha(out/'MshrObserved.sv'),'defines':DEFINES,
        'source_cuts':False,'capacities_changed':False,'top':'MshrObserved',
        'yosys':str(args.yosys.resolve()),'yosys_sha256':sha(args.yosys.resolve())}
    (out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    started=time.monotonic()
    with (out/'baseline.log').open('w') as log:
        proc=subprocess.run([str(args.yosys.resolve()),'-m','slang','-s',str(script)],stdout=log,stderr=subprocess.STDOUT,timeout=180)
    manifest.update(status='complete' if proc.returncode==0 else 'failed',returncode=proc.returncode,seconds=time.monotonic()-started)
    if proc.returncode==0:
        design=json.loads((out/'baseline.json').read_text())['modules']['MshrObserved']
        manifest['cell_counts']={typ:sum(c['type']==typ for c in design['cells'].values()) for typ in sorted({c['type'] for c in design['cells'].values()})}
        manifest['port_bits']={d:sum(len(p['bits']) for p in design['ports'].values() if p['direction']==d) for d in ['input','output']}
    (out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps(manifest,indent=2))
    if proc.returncode:raise SystemExit(proc.returncode)

if __name__=='__main__':main()
