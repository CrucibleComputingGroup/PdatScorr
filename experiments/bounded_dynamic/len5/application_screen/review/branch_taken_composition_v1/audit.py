#!/usr/bin/env python3
"""Read-only branch-cut addendum: in-memory structure checks, no backend."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
APP = HERE.parents[1]
sys.path[:0] = [str(APP.parents[3]), str(APP)]
import abstract_datapath as abstraction
import domain_lemmas as lemmas

def read(path): return json.loads(Path(path).read_text())
def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def main():
    certpath = APP.parent/'isa_baseline/results/program_alphabet_certificate_v3.json'
    cert = read(certpath); domain = Path(cert['domain_summary'])
    paths = {'audit': Path(__file__), 'helper': Path(abstraction.__file__),
        'lemma_helper': Path(lemmas.__file__), 'certificate': certpath,
        'native_original': Path(cert['native_original_json']),
        'native_candidate': Path(cert['native_candidate_json']), 'domain_summary': domain,
        'projection': domain.parent/'data_path.json',
        'rom_proof': APP/'evidence/rom_domain_v2/summary.json',
        'previous_review': HERE.parent/'alu_mul_composition_v1/summary.json'}
    sources = {name: {'path': str(path.resolve()), 'sha256': sha(path)} for name,path in paths.items()}
    assert sources['native_original']['sha256'] == cert['native_original_sha256']
    assert sources['native_candidate']['sha256'] == cert['native_candidate_sha256']
    assert sources['domain_summary']['sha256'] == cert['domain_summary_sha256']
    assert sources['projection']['sha256'] == cert['domain_projection_json_sha256']
    native, original = read(paths['native_candidate']), read(paths['native_original'])
    projection, dom = read(paths['projection']), read(domain)
    bound = lemmas.native_lemma_bindings(original, native, projection, dom['projection'])
    allowed = {int(word,16) for word in read(paths['rom_proof'])['domain_words']}
    with_lemmas, added = lemmas._add_domain_assumptions(native, bound, allowed)
    result, audit = abstraction.abstract_datapath(with_lemmas, 'datapath', 'alu_mul_branch_taken')
    abstract_first, _ = abstraction.abstract_datapath(native, 'datapath', 'alu_mul_branch_taken')
    commute, _ = lemmas._add_domain_assumptions(abstract_first, bound, allowed)
    assert commute == result
    cuts = {cut['original_cell_name'] for cut in audit['cuts']}
    assert cuts == {'$procmux$11115', '$procmux$7848', '$procmux$20161'}
    branch = audit['cuts'][2]
    assert branch['target'] == 'branch_taken' and branch['width'] == 1 and branch['output_bits'] == [46726]
    a, b = with_lemmas['modules']['datapath'], result['modules']['datapath']
    assert all(b['cells'][name] == cell for name,cell in a['cells'].items() if name not in cuts)
    assert all(a[key] == b[key] for key in a if key != 'cells')
    state = {name:cell for name,cell in a['cells'].items() if abstraction._state_cell(cell)}
    assert all(b['cells'][name] == cell for name,cell in state.items())
    projection_cells = set(dom['projection']['original_cell_slices']) | set(dom['projection']['retained_spill_write_control_cells'])
    overlap = sorted(cuts & projection_cells); lemma_overlap = sorted(cuts & set(added))
    projection_inputs = {bit for cell in projection['modules']['InstructionDataPath']['cells'].values()
        for pin,bits in cell['connections'].items() if cell['port_directions'][pin] == 'input' for bit in bits}
    consumers = []
    for name,cell in a['cells'].items():
        pins = {pin: sorted(set(branch['output_bits']) & set(bits)) for pin,bits in cell['connections'].items()
            if cell['port_directions'][pin] == 'input' and set(branch['output_bits']) & set(bits)}
        if pins: consumers.append({'cell':name,'type':cell['type'],'pins':pins,'source':cell.get('attributes',{}).get('src')})
    source_pin = '14291dcc5bef181085d001c5a29e7f4fc4cbc8e9'
    command = ['git','-C','/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/deps/len5',
        'show',source_pin+':rtl/expipe/exec-units/branch_unit.sv']
    rtl = subprocess.run(command,check=True,capture_output=True).stdout
    (HERE/'branch_unit.sv').write_bytes(rtl)
    for name,path in paths.items(): assert sha(path) == sources[name]['sha256'], name
    record = {'status':'read_only_branch_composition_review_passed','new_backend_queries':0,
        'accepted_optimization':False,'sources':sources,'mode':'alu_mul_branch_taken',
        'rtl_source_command':command,'rtl_source_sha256':hashlib.sha256(rtl).hexdigest(),
        'branch_cut':branch,'direct_branch_consumers':consumers,
        'fresh_symbolic_bits_per_cycle':audit['fresh_symbolic_bits_per_cycle'],
        'native_cell_count':len(native['modules']['datapath']['cells']),
        'native_state_cells_unchanged':len(state),'native_cells_unchanged_except_cuts':len(native['modules']['datapath']['cells'])-len(cuts),
        'lemma_encoding_cells_unchanged':len(added),'lemma_assumptions_unchanged':7,
        'ports_aliases_module_attributes_unchanged':True,
        'native_projection_cell_overlap':overlap,'lemma_encoding_cell_overlap':lemma_overlap,
        'branch_bit_occurs_as_projection_cell_input':bool(set(branch['output_bits']) & projection_inputs),
        'commutes_with_lemma_addition':True,'abstract_structural_sha256':audit['abstract_structural_sha256'],
        'trace_inclusion':'For each original constrained trace, choose all three fresh outputs equal to the original ALU result, MUL result, and branch outcome each cycle. All original state, retained equations, and already-proved word-domain lemmas then agree. Therefore the restricted abstract model includes every original constrained trace.',
        'qualification':'The scalar branch outcome is deliberately relaxed, including the possibility of not-taken unconditional jumps. This can change misprediction, target-alignment exceptions, recovery, and later control paths on abstract traces. Such traces may be spurious. This audit proves no admission bound and no hardware saving.',
        'projection_scope':'No projected data/control cell or input bit overlaps the third cut in this exact model. More generally overlap would require recording altered projection behavior, but would not refute original-trace inclusion when the imported lemmas are independently established on the original design first.'}
    (HERE/'summary.json').write_text(json.dumps(record,indent=2)+'\n')
    (HERE/'abstract_datapath.py').write_bytes(paths['helper'].read_bytes())
    print(json.dumps({k:record[k] for k in ['status','fresh_symbolic_bits_per_cycle','native_state_cells_unchanged',
        'native_projection_cell_overlap','lemma_encoding_cell_overlap','branch_bit_occurs_as_projection_cell_input','commutes_with_lemma_addition']}))

if __name__ == '__main__': main()
