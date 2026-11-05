#!/usr/bin/env python3
"""Time-limited GLA on the closed 48-premise, native-arithmetic cube query.

The unchanged qualified gate_solver engine owns folding, verdict parsing and
counterexample validation. This wrapper adds no premise or hardware rewrite.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import shutil

import gate_solver
import reset_cube_prepared
import register_status_prepared
import solve_prepared
from gate_solver import digest, require

YOSYS='/home/allenjin/Projects/DAC_pscorr/tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys'
RECORDS=('native_word_domain_import','external_rom_domain_import','inactive_fu_import',
         'register_status_import','reset_cube_import')


def validate_combined(directory):
    directory=Path(directory).resolve()
    model=reset_cube_prepared.validate_reset_cube_prepared(directory)
    require(model['abstraction_mode']=='none' and model['datapath_abstraction'] is None,
            'Native arithmetic required')
    require(model['query_property_counts']=={'assert':3,'assume':48,'cover':0},
            'Exactly three assertions and48assumptions required')
    require(model['instruction_model']=='immutable_rom' and model['instruction_fault_payload']=='zero',
            'Exact immutable zero-fault ROM required')
    require(Path(model['query_core_path']).resolve()==directory/'reset_cube_query_core.json',
            'Exact combined cube graph required')
    dependencies={}
    for name in RECORDS:
        for path,expected in model[name]['proof_dependencies_sha256'].items():
            require(path not in dependencies or dependencies[path]==expected,'Conflicting proof dependency')
            dependencies[path]=expected
    for path,expected in dependencies.items():
        require(model['native_word_domain_import']['proof_dependencies_sha256'].get(path)==expected,
                'Incomplete transitive proof closure')
        require(digest(Path(path))==expected,'Proof dependency changed: '+path)
    return model,dependencies


def qualification_source(include_last):
    assumptions='\n'.join(f'assume(!d[{i}]);' for i in range(48 if include_last else 47))
    return '''module GateToy(input clk, input [47:0] d);
reg q; reg seen=0;
always @(posedge clk) begin q <= |d; seen <= 1; end
always @* begin
'''+assumptions+'''
if(seen) assert(!q);
end
endmodule
'''


def qualify_48(directory, *, yosys=YOSYS, abc='/usr/local/bin/abc'):
    directory=Path(directory).resolve();directory.mkdir(parents=True,exist_ok=False)
    cases={}
    for name,last,expected in [('all48',True,'proved_safety_query_only'),
                               ('without_last',False,'counterexample_in_query_model')]:
        aig,prepared=gate_solver.prepare_toy(qualification_source(last),directory/(name+'_model'),yosys=yosys)
        require(int(prepared['aig_header'][7])==(48 if last else 47),'Qualification constraint inventory changed')
        result=gate_solver.run_gla(aig,directory/(name+'_gla'),abc=abc,timeout=5)
        require(result['status']==expected,'48-constraint qualification failed: '+name)
        if not last:
            require(result['counterexample_validation']['returncode']==0,
                    'Missing-last-constraint witness not validated')
        cases[name]={'preparation':prepared,'result':result}
    record={'status':'qualified','cases':cases,'last_constraint_is_necessary':True,
            'scope':'Real installed frontend and GLA; positive has48constraints, negative omits only d[47]==0. '
                    'Unknown initial q is preserved and observation begins after its first update.'}
    record['artifacts_sha256']={str(p.relative_to(directory)):digest(p) for p in directory.rglob('*') if p.is_file()}
    (directory/'summary.json').write_text(json.dumps(record,indent=2)+'\n')
    return record


def run_combined(prepared,output,*,abc='/usr/local/bin/abc',yosys=YOSYS,timeout=600):
    require(0<timeout<=600,'Budget must be positive and at most600seconds')
    prepared,output=Path(prepared).resolve(),Path(output).resolve()
    model,dependencies=validate_combined(prepared)
    binding=digest(prepared/'summary.json')
    drivers=[Path(__file__),Path(gate_solver.__file__),Path(reset_cube_prepared.__file__),
             Path(register_status_prepared.__file__),Path(solve_prepared.__file__)]
    driver_hashes={str(p.resolve()):digest(p) for p in drivers}
    snapshots={p.name:p.read_bytes() for p in drivers}
    binaries={str(Path(shutil.which(p) or p).resolve()):digest(Path(shutil.which(p) or p)) for p in (abc,yosys)}
    output.mkdir(parents=True,exist_ok=False)
    qualification=qualify_48(output/'qualification',yosys=yosys,abc=abc)
    # Recheck immediately before the single target call, after qualification.
    _,fresh=validate_combined(prepared)
    require(fresh==dependencies and digest(prepared/'summary.json')==binding,'Preparation changed during qualification')
    for path,expected in {**driver_hashes,**binaries}.items():
        require(digest(Path(path))==expected,'Driver/tool changed before target: '+path)
    result=gate_solver.run_gla(prepared/'screen.aig',output/'gla',abc=abc,timeout=timeout)
    result.update(prepared_directory=str(prepared),prepared_summary_sha256=binding,
        requested_seconds=timeout,query_property_counts=model['query_property_counts'],
        abstraction_mode='none',proof_dependencies_sha256=dependencies,
        wrapper_dependencies_sha256=driver_hashes,tool_dependencies_sha256=binaries,
        native_hardware_json_sha256=model['core_json_sha256'],query_model_sha256=model['query_core_sha256'],
        qualification_summary_sha256=digest(output/'qualification/summary.json'),
        qualification_status=qualification['status'],source_reset_facts={'inactive':1761,'register_status':275,'cube':583},
        native_query_scope='Native arithmetic and original controls retained; existing closed program-only lemmas only. '
            'The three safety obligations remain the acceptance target. No new premise, payload cut, physical model change '
            'or hardware savings claim. A validated CEX belongs to the original folded formal query, not automatically '
            'to a concrete benchmark execution. No automatic PDR or continuation.')
    try:
        final,final_dependencies=validate_combined(prepared)
        require(final_dependencies==dependencies and digest(prepared/'summary.json')==binding,
                'Preparation or proof closure changed during GLA')
        require(final['aig_sha256']==result['input_aig_sha256'],'Solved AIG differs from preparation')
        for path,expected in {**driver_hashes,**binaries}.items():
            require(digest(Path(path))==expected,'Driver/tool changed during GLA: '+path)
        for relative,expected in qualification['artifacts_sha256'].items():
            require(digest(output/'qualification'/relative)==expected,'Qualification artifact changed: '+relative)
        require(digest(output/'qualification/summary.json')==result['qualification_summary_sha256'],
                'Qualification record changed')
        result['post_run_dependencies_verified']=True
    except (ValueError,OSError,KeyError) as error:
        result.update(status='error',error=str(error),post_run_dependencies_verified=False)
    for name,content in snapshots.items():
        target=output/'wrapper_sources'/name;target.parent.mkdir(exist_ok=True);target.write_bytes(content)
    result['wrapper_artifacts_sha256']={str(p.relative_to(output)):digest(p) for p in (output/'wrapper_sources').iterdir()}
    result['gla_summary_sha256']=digest(output/'gla/summary.json')
    (output/'summary.json').write_text(json.dumps(result,indent=2)+'\n')
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepared',type=Path,required=True);parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--abc',default='/usr/local/bin/abc');parser.add_argument('--yosys',default=YOSYS)
    parser.add_argument('--timeout',type=int,default=600)
    args=parser.parse_args();result=run_combined(args.prepared,args.output,abc=args.abc,yosys=args.yosys,timeout=args.timeout)
    print(json.dumps({'status':result['status'],'accepted_optimization':False}))


if __name__=='__main__':main()
