#!/usr/bin/env python3
"""One conditional component query with an explicit tag-ownership monitor.

This protocol is not yet certified on the native LEN5 allocator. A successful
query is an intermediate conditional result, never an accepted core rewrite.
"""
from __future__ import annotations
import argparse
import copy
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[3]))
from odc.temporal import checked_yosys, digest, run_command, yosys_path
from guard_invariants import export_smt


MONITOR = '''module UniqueTagProtocol(
 input clk_i, rst_ni, flush_i,
 input issue_valid_i, issue_ready_i, input [4:0] issue_tag_i,
 input complete_valid_i, complete_ready_i, input [4:0] complete_tag_i
);
 reg [31:0] outstanding;
 wire allocate = issue_valid_i && issue_ready_i;
 wire release_tag = complete_valid_i && complete_ready_i;
 wire available = !outstanding[issue_tag_i] ||
                  (release_tag && complete_tag_i == issue_tag_i);
 always @* if (rst_ni && !flush_i && allocate) assume (available);
 always @(posedge clk_i or negedge rst_ni) begin
   if (!rst_ni) outstanding <= 0;
   else if (flush_i) outstanding <= 0;
   else begin
     if (release_tag) outstanding[complete_tag_i] <= 0;
     if (allocate) outstanding[issue_tag_i] <= 1;
   end
 end
endmodule
'''


def add_monitor(design):
    out = copy.deepcopy(design)
    module = out['modules']['BankMiter']
    nets = module['netnames']
    def bits(name, width):
        b = nets[name]['bits']
        if len(b) != width:
            raise ValueError('Unexpected native interface width: ' + name)
        return b
    connection = {
        'clk_i': bits('clk_i', 1), 'rst_ni': bits('rst_ni', 1),
        'flush_i': bits('flush_i', 1), 'issue_valid_i': bits('issue_valid_i', 1),
        'issue_ready_i': bits('ref_issue_ready_o', 1),
        'issue_tag_i': bits('issue_dest_rob_idx_i', 5),
        'complete_valid_i': bits('reference.alu_valid', 1),
        'complete_ready_i': bits('ref_cdb_ready_o', 5)[2:3],
        'complete_tag_i': bits('reference.alu_data', 75)[70:75],
    }
    if 'unique_tag_protocol' in module['cells']:
        raise ValueError('Protocol monitor already exists')
    module['cells']['unique_tag_protocol'] = {
        'hide_name': 0, 'type': 'UniqueTagProtocol', 'parameters': {},
        'attributes': {'pscorr_proof_only': 1}, 'connections': connection,
        'port_directions': {name: 'input' for name in connection},
    }
    return out, connection


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-native', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--timeout', type=int, default=120)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True)
    workspace = next(p for p in HERE.parents if (p/'tools/oss-cad-suite-20261104').exists())
    yosys = str(workspace/'tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys')
    smtbmc = str(Path(yosys).with_name('yosys-smtbmc'))
    source = args.source_native.resolve()
    original = json.loads(source.read_text())
    modified, connections = add_monitor(original)
    (out/'conditional_protocol_source.py').write_bytes(Path(__file__).read_bytes())
    (out/'UniqueTagProtocol.sv').write_text(MONITOR)
    (out/'instrumented.json').write_text(json.dumps(modified)+'\n')
    summary = {
        'status': 'running', 'conditional_proven': False, 'accepted_rewrites': 0,
        'source_native': str(source), 'source_native_sha256': digest(source),
        'implementation_sha256': digest(Path(__file__)),
        'monitor_sha256': digest(out/'UniqueTagProtocol.sv'),
        'bindings': connections, 'assumptions_added': 1,
        'scope': 'Conditional ALU+CDB component only. Native ROB/issue protocol closure is NOT proved.',
        'protocol': 'Accepted ALU issue reserves its ROB tag until local ALU CDB ready/valid completion or flush/reset. Same-edge completion/reallocation is allowed. No operand/readiness/service restriction.',
        'source_bit_bindings': 'PRE-FPU expipe_pkg.sv cdb_data_t has ROB tag at bits74:70; EU_INT_ALU=3 means normal CDB slot2. Original wrapper and full raw local ALU payload retained.',
    }
    def save():
        (out/'summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    save()
    summary['prepare'] = checked_yosys(yosys,
        f'read_json {yosys_path(out/"instrumented.json")}\n'
        f'read_verilog -formal -sv {yosys_path(out/"UniqueTagProtocol.sv")}\n'
        'hierarchy -top BankMiter\nproc\nflatten\ncheck -assert\n'
        f'write_json {yosys_path(out/"native.json")}\n', out, 'prepare', 60)
    native = json.loads((out/'native.json').read_text())
    _, meta = export_smt(native, 'BankMiter', out/'joint', yosys)
    if meta['property_counts']['assume'] != 2:
        raise ValueError('Expected precisely original initial-reset plus ownership premise')
    summary['joint'] = meta
    aig = out/'joint/model.aig'
    meta['aig_export'] = checked_yosys(yosys,
        f'read_json {yosys_path(out/"joint/lowered.json")}\nchformal -cover -remove\nformalff -clk2ff\n'
        'setundef -anyseq\nopt -keepdc\ntechmap\nopt -keepdc\nsetundef -anyseq\nabc -g AND\naigmap\n'
        f'write_aiger -zinit -symbols {yosys_path(aig)}\n', out/'joint', 'aig_export', 60)
    with aig.open('rb') as stream:
        header = stream.readline().decode('ascii').split()
    if header[0] != 'aig' or len(header)<8 or int(header[4]) or int(header[7]) != 2 or any(int(x) for x in header[8:]):
        raise ValueError('Expected safety model with exactly two constraints')
    meta['aig_sha256'] = digest(aig)
    meta['aig_bad_properties'], meta['aig_constraints'] = int(header[6]), int(header[7])
    save()
    command = f'read_aiger "{aig}"; fold; orpos; pdr -T {args.timeout} -v'
    result = run_command(['/usr/local/bin/abc','-c',command], out/'joint/pdr.log',args.timeout+5)
    log = (out/'joint/pdr.log').read_text()
    meta['pdr'] = result
    summary['conditional_proven'] = result['returncode']==0 and not result['timeout'] and bool(re.search(r'(?m)^Property proved\.', log)) and not re.search(r'\b(error|failed|undecided|disproved|timed out|time limit|was asserted)\b',log,re.I)
    summary['status'] = 'conditional_component_proved' if summary['conditional_proven'] else 'conditional_component_not_proven'
    save()
    negative = out/'negative_protocol'
    negative.mkdir()
    negative_source = MONITOR.replace('assume (available)', 'assert (available)').replace(
        ' reg [31:0] outstanding;', ' always @* if ($initstate) assume (!rst_ni);\n reg [31:0] outstanding;')
    (negative/'monitor.sv').write_text(negative_source)
    summary['negative_protocol'] = checked_yosys(yosys,
        f'read_verilog -formal -sv {yosys_path(negative/"monitor.sv")}\nprep -top UniqueTagProtocol\nasync2sync\ndffunmap\n'
        f'write_smt2 -wires {yosys_path(negative/"model.smt2")}\n', negative, 'prepare', 30)
    neg = run_command([smtbmc,'-s','z3','-t','4','--noprogress','--dump-vcd',str(negative/'counterexample.vcd'),str(negative/'model.smt2')], negative/'bmc.log',30)
    neglog = (negative/'bmc.log').read_text()
    summary['negative_protocol'].update({'run':neg, 'explicit_assertion_counterexample':neg['returncode']==1 and 'Assert failed' in neglog and 'Status: FAILED' in neglog, 'scope':'Standalone protocol monitor negative, not a bank-rewrite counterexample'})
    if digest(source) != summary['source_native_sha256'] or digest(Path(__file__)) != summary['implementation_sha256']:
        summary.update(conditional_proven=False,status='source_changed_during_run')
    save()
    print(json.dumps({'status':summary['status'],'accepted_rewrites':0,'negative_monitor_witness':summary['negative_protocol']['explicit_assertion_counterexample']}))


if __name__ == '__main__':
    main()
