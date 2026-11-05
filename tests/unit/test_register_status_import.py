"""Native transport, fresh RD encodings and source-bound importer rejection."""
import copy
from pathlib import Path
import sys
import pytest

ROOT=Path(__file__).resolve().parents[2]
APP=ROOT/'experiments/bounded_dynamic/len5/application_screen'
sys.path[:0]=[str(ROOT),str(APP)]
import register_status_import as importer

BUILD=Path('/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build')
YOSYS='/home/allenjin/Projects/DAC_pscorr/tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys'


@pytest.fixture(scope='module')
def objects():
    prep=BUILD/'harvard_rom_inactive_fu_native_prepare_v1'
    if not prep.exists():pytest.skip('Frozen native composition unavailable')
    r=importer.read(prep/'summary.json')
    return dict(original=importer.read(prep/'source.json'),
        decoder=importer.read(BUILD/'program_alphabet_v1/candidate_whole_core.json'),
        reduced=importer.read(BUILD/'inactive_fu_lemmas_v1/query_only.json'),
        current=importer.read(prep/'inactive_query_core.json'),word_import=r['native_word_domain_import'],
        inactive_import=r['inactive_fu_import'],rom_import=r['external_rom_domain_import'],
        local=importer.read(BUILD/'register_status_lemmas_v2/summary.json'))


def compose(objects):
    return importer.compose_query(**{k:v for k,v in objects.items() if k!='rom_import'})


def test_exact_composition_preserves_word_predicates_and_visible_fields(objects):
    query,record=compose(objects)
    assert record['proof_only_property_counts']=={'assert':0,'assume':47,'cover':0}
    assert len(record['rd_encoding']['added_cells'])==360
    assert len(record['original_rd_projection_cells_changed_by_preceding_closed_rewrites'])==10
    assert record['native_component_cells_identical']==506
    before=objects['current']['modules']['datapath']['cells'];after=query['modules']['datapath']['cells']
    assert all(before[n]==after[n] for n in objects['word_import']['added_cells'])
    old_bits={b for c in before.values() for bs in c['connections'].values() for b in bs if type(b) is int}
    assert record['rd_encoding']['fresh_bit_min']>max(old_bits)
    for i,field in enumerate(objects['local']['rd_theorem_chain']['unique_stored_field_lemmas']):
        assert after[f'$pscorr_rd_lemma_{i}_value_0']['connections']['A']==field['bits']


def test_modified_component_rejected(objects):
    changed=copy.deepcopy(objects)
    name=objects['local']['native_component_audit']['unused_entries'][0]['fields'][0]['native_cell']
    for key in ('current','reduced'):
        changed[key]['modules']['datapath']['cells'][name]['connections']['AD'][0]='1'
    with pytest.raises(ValueError,match='component changed'):compose(changed)


def test_unexplained_query_change_rejected(objects):
    changed=copy.deepcopy(objects)
    changed['current']['modules']['datapath']['ports']['probe_index']['bits'][0]='0'
    with pytest.raises(ValueError,match='Current graph differs'):compose(changed)


def test_rd_field_reset_overlap_rejected(objects):
    changed=copy.deepcopy(objects)
    bit=changed['local']['rd_theorem_chain']['unique_stored_field_lemmas'][0]['bits'][0]
    changed['inactive_import']['reset_substitutions'][str(bit)]='0'
    with pytest.raises(ValueError,match='overlap native RD'):compose(changed)


def test_missing_rom_closure_rejected(objects,tmp_path):
    with pytest.raises(ValueError,match='Closed preceding'):
        importer.import_register_status(BUILD/'register_status_lemmas_v2',objects['original'],objects['decoder'],objects['reduced'],
            objects['current'],objects['word_import'],objects['inactive_import'],{'status':'unproved'},tmp_path/'import',yosys=YOSYS)


def test_actual_closed_export_replay_no_solver(objects,tmp_path):
    if not Path(YOSYS).exists():pytest.skip('Pinned formal frontend unavailable')
    query,record=importer.import_register_status(BUILD/'register_status_lemmas_v2',objects['original'],objects['decoder'],objects['reduced'],
        objects['current'],objects['word_import'],objects['inactive_import'],objects['rom_import'],tmp_path/'import',yosys=YOSYS)
    assert record['derived_assumptions_added']==40 and record['proved_reset_bits_substituted']==275
    assert record['rf_candidate_substituted'] is False
    assert record['new_unproved_internal_premises']==0
    importer.verify_dependencies(record)
