#!/usr/bin/env python3
"""Copy compact, hash-checked finite fetch-spacing evidence without wave files."""
import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from prepare_frontend import digest,workspace_root


def hex_image(path):
    image={};address=0
    for token in path.read_text().split():
        if token.startswith('@'):address=int(token[1:],16)
        else:image[address]=int(token,16);address+=1
    return image


def main():
    here=Path(__file__).resolve().parent;root=here.parent
    external=workspace_root(here)/'experiments/bounded_dynamic/len5/build'
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--workload-version',type=int,choices=(1,2),default=2,
                    help='Version1 retains the speculative fault; version2 explicitly maps padding RAM')
    args=ap.parse_args();out=args.output.resolve();out.mkdir(parents=True,exist_ok=False)
    version=args.workload_version
    pairs=[('native',f'streaming_v{version}','pre_fpu_simulation_ooo'),
           ('fetch_gap2',f'streaming_fetchgap2_v{version}','pre_fpu_simulation_fetchgap2_v1')]
    copies=[];records={};manifests={}
    def copy(source,destination):
        destination.parent.mkdir(parents=True,exist_ok=True)
        destination.write_bytes(source.read_bytes())
        sha=digest(destination.read_bytes());assert sha==digest(source.read_bytes())
        copies.append({'path':str(destination.relative_to(out)),'source':str(source.resolve()),'sha256':sha})
    files=('summary.json','platform_timing_summary.json','accepted_stores.csv','occupancy.csv',
           'native_platform_edges.csv','fetch_response_intervals.csv','load_response_intervals.csv',
           'program.S','program.hex','program.disasm','run.log','logs/qualification_events.csv')
    for label,run_name,build_name in pairs:
        source=root/'results'/run_name
        record=json.loads((source/'platform_timing_summary.json').read_text())
        manifest=json.loads((external/build_name/'manifest.json').read_text())
        assert record['simulator_manifest_sha256']==digest((external/build_name/'manifest.json').read_bytes())
        assert record['all_64_output_stores_and_exit_checked']
        assert not record['full_trace']['fetch_faults']
        faults=record['full_trace']['load_faults']
        if version==2:assert not faults
        else:
            assert len(faults)==1 and faults[0]['address']==0x1200
            assert faults[0]['exception']==1 and faults[0]['exception_code']==5
        assert record['dynamic_issue']['witness_found']
        for file,expected in record['artifact_sha256'].items():
            assert digest((source/file).read_bytes())==expected
        for file in files:copy(source/file,out/label/file)
        copy(external/build_name/'manifest.json',out/label/'simulator_manifest.json')
        records[label]=record;manifests[label]=manifest
    assert manifests['native']['core_source_sha256']==manifests['fetch_gap2']['core_source_sha256']
    for key in ('capacity_parameters','memory_pipe_num','fetch_fifo_depth','upstream_commit'):
        assert manifests['native'][key]==manifests['fetch_gap2'][key]
    for name in ('instruction_spacing_gate.svh','platform_monitor.svh'):
        source=external/'pre_fpu_simulation_fetchgap2_v1/source/tb'/name
        assert digest(source.read_bytes())==manifests['fetch_gap2']['platform_source_sha256'][name]
        copy(source,out/'platform'/name)
    copy(root/f'results/streaming_fetchgap2_v{version}/logs/platform_edges.csv',out/'fetch_gap2/logs/platform_edges.csv')
    original=hex_image(root/'results/streaming_v1/program.hex')
    padded=hex_image(root/'results/streaming_v2/program.hex')
    assert original=={k:v for k,v in padded.items() if k in original}
    extra={k:v for k,v in padded.items() if k not in original}
    assert set(extra)==set(range(0x1200,0x1280)) and set(extra.values())=={0}
    assert (root/f'results/streaming_v{version}/program.hex').read_bytes()==(root/f'results/streaming_fetchgap2_v{version}/program.hex').read_bytes()
    note={'scope':'Finite same-core/same-program platform comparison; no proof or area claim',
          'workload_version':version,
          'exception_free_platform_qualified':version==2,
          'core_sources_identical':True,'capacities_identical':True,'program_images_identical':True,
          'padding_audit':{'all_v1_bytes_preserved':True,'new_zero_bytes':len(extra),
                           'range_start':0x1200,'range_end_exclusive':0x1280,
                           'reason':'Version2 initializes speculative load beyond 64 input words; version1 fault trace retained separately'},
          'rows':[{ 'platform':label,'reported_cpu_cycles':r['reported_cpu_cycles'],
                    'max_alu_live':r['max_alu_live_post_edge'],'allocated_alu_indices':r['used_alu_allocation_indices'],
                    'fetch_latencies':r['full_trace']['fetch_latency_histogram'],
                    'load_latencies':r['full_trace']['load_latency_histogram'],
                    'load_faults':r['full_trace']['load_faults'],
                    'ooo_inversions':r['dynamic_issue']['actual_alu_issue_inversion_count']}
                  for label,r in records.items()],
          'reported_cycle_ratio':records['fetch_gap2']['reported_cpu_cycles']/records['native']['reported_cpu_cycles'],
          'files':copies}
    (out/'comparison.json').write_text(json.dumps(note,indent=2)+'\n')
    hashes=[(x['path'],x['sha256']) for x in copies]+[('comparison.json',digest((out/'comparison.json').read_bytes()))]
    (out/'SHA256SUMS').write_text(''.join(f'{sha}  {name}\n' for name,sha in sorted(hashes)))
    print(json.dumps({'copied_files':len(copies),'bytes':sum(p.stat().st_size for p in out.rglob('*') if p.is_file()),
                      'rows':note['rows']}))


if __name__=='__main__':main()
