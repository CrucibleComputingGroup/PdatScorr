#!/usr/bin/env python3
"""Prepare matched original, assumed, and proved-cut actual RSD LQ/SQ runs."""
import argparse, hashlib, importlib.util, json, re
from pathlib import Path
root=Path(__file__).resolve().parents[3]
base=root/'experiments/rsd_ooo'
src=base/'rsd/Processor/Src'
files=(base/'formal/rtl_sources.txt').read_text().splitlines()
spec=importlib.util.spec_from_file_location('gen',root/'code/PdatProject/ScorrPdat/scripts/make_synthesis_script.py')
gen=importlib.util.module_from_spec(spec);spec.loader.exec_module(gen)
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--variants',nargs='+',choices=['original','region_assume','region_cut','region_lemmas'],default=['original','region_assume','region_cut'])
parser.add_argument('--mask-reset-outputs',action='store_true',help='Observe every wrapper output only while rst is low; preserve all original internal reset logic/transitions')
args=parser.parse_args()
for variant in args.variants:
 out=base/'results/synthesis'/('lsq_'+variant+('_reset_observed' if args.mask_reset_outputs else ''))
 if out.exists(): raise SystemExit(f'Refusing existing {out}')
 out.mkdir()
 source_files=[]
 proof_import=None
 if variant=='region_lemmas':
  proof_variant=base/'results/synthesis/isa_region_lemmas_core_final'
  proof_import=json.loads((proof_variant/'proof_import.json').read_text())
  proof_manifest=json.loads((proof_variant/'manifest.json').read_text())
  proof_summary=Path(proof_import['proof_summary'])
  assert hashlib.sha256(proof_summary.read_bytes()).hexdigest()==proof_import['proof_summary_sha256']
 for f in files:
  if variant=='region_lemmas' and Path(f).name in ['LoadQueue.sv','StoreQueue.sv']:
   candidate=proof_variant/'src'/f
   assert hashlib.sha256(candidate.read_bytes()).hexdigest()==proof_manifest['source_files'][f]
   source_files.append(candidate)
  else:
   source_files.append((base/'formal/generated'/Path(f).name) if variant=='region_cut' and Path(f).name in ['LoadQueue.sv','StoreQueue.sv'] else src/f)
 harness=(base/'formal/LSQObserved.sv').read_text()
 if args.mask_reset_outputs:
  output_names=[]
  for line in harness.splitlines():
   match=re.match(r'\s*output logic\s+(?:\[[^\]]+\]\s+)?(.+)',line)
   if match:
    output_names.extend(name.strip() for name in match[1].rstrip(',').split(','))
  assert len(output_names)==18 and all(re.fullmatch(r'[a-zA-Z_][a-zA-Z_0-9]*',name) for name in output_names),output_names
  marker='        observed_forward_miss = lsu.storeLoadForwarded[0] && lsu.forwardMiss[0];'
  assert harness.count(marker)==1
  mask='\n        // Observation is disabled during reset; internal reset transitions remain.\n        if (rst) begin\n'+''.join("            "+name+" = '0;\n" for name in output_names)+'        end'
  harness=harness.replace(marker,marker+mask)
 if variant in ['region_assume','region_lemmas']:
  harness=harness.replace('endmodule', '''always_comb begin
    if (!rst && execute_load) assume(load_address[21:16] == 6'b0);
    if (!rst && execute_store) assume(store_address[21:16] != 6'b0);
  end
endmodule''')
 (out/'LSQObserved.sv').write_text(harness)
 defines=['RSD_SYNTHESIS','RSD_SYNTHESIS_DESIGN_COMPILER','REF=input','RSD_DISABLE_DEBUG_REGISTER','RSD_DISABLE_PERFORMANCE_COUNTER','RSD_MARCH_INT_ISSUE_WIDTH=2','RSD_MARCH_FP_PIPE','RSD_ENABLE_ZBA','RSD_ENABLE_ZICOND']
 frontend='read_slang --single-unit --top LSQObserved -I'+str(src)+' '+' '.join('-D'+d for d in defines)+' '+' '.join(map(str,source_files+[out/'LSQObserved.sv']))+'\n'
 commands=gen._generate_synthesis_commands('LSQObserved',str(out/'core'))
 (out/'synth.ys').write_text(frontend+'chformal -lower\nchformal -assert -remove\n'+commands)
 (out/'manifest.json').write_text(json.dumps({'scope':'Actual RSD LQ+SQ component, NOT whole-core area','variant':variant,'contract':'Every executed load address[21:16]==0 and every executed store address[21:16]!=0 after reset, including invalid/reg-invalid/wrong-path operations','source_sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in source_files},'harness_sha256':hashlib.sha256(harness.encode()).hexdigest(),'defines':defines,'observation':'All queue status/allocation, store-commit and LQ conflict outputs; forwarding data/miss qualified by forwarded flag','initialization':'Pscorr inherited setundef -zero and AIGER -zinit; no state cycling'},indent=2)+'\n')
 if proof_import is not None:
  (out/'proof_import.json').write_text(json.dumps(proof_import,indent=2)+'\n')
 if args.mask_reset_outputs:
  manifest_path=out/'manifest.json';manifest=json.loads(manifest_path.read_text());manifest['reset_observation']='All 18 wrapper output ports (144 bits) forced zero while rst high; original internal reset transitions and same-cycle logic retained';manifest_path.write_text(json.dumps(manifest,indent=2)+'\n')
 print(out)
