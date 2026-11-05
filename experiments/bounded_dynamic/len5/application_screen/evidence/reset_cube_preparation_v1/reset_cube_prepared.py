"""Strict validation of the combined native-arithmetic cube preparation.

This creates no solver entry point and preserves all earlier family guards.
"""
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE.parents[3]),str(HERE)]
from domain_lemmas import verify_dependencies as verify_words
from inactive_fu_import import verify_dependencies as verify_inactive
from register_status_import import verify_dependencies as verify_registers
from register_status_prepared import validate_register_status_prepared
from reset_cube_import import verify_dependencies as verify_cube
from register_status_lemmas import digest,read,require
from rom_domain_import import verify_dependencies as verify_rom


def validate_reset_cube_prepared(directory):
    directory=Path(directory).resolve();record=read(directory/'summary.json')
    require(record['status']=='prepared_query_only' and record['accepted_optimization'] is False
        and record['engine']=='prepare','Only a completed preparation is eligible')
    require(record['abstraction_mode']=='none' and record['datapath_abstraction'] is None,'Native arithmetic required')
    require(record['native_hardware_contains_formal_properties'] is False,'Native export must remain separate')
    require(record['query_property_counts']=={'assert':3,'assume':48,'cover':0},'Original3assert/48assume inventory required')
    cube=record['reset_cube_import']
    require(cube['status']=='closed_reset_cube_delta_imported' and cube['assumptions_added']==0
        and cube['proved_reset_words_substituted']==42 and cube['proved_reset_bits_substituted']==583
        and cube['new_environmental_premises']==[] and cube['new_unproved_internal_premises']==0,
        'Closed delta-only cube proof required')
    reference=Path(cube['reference_prepared_directory'])
    prior=validate_register_status_prepared(reference)
    require(digest(reference/'summary.json')==cube['reference_summary_sha256'],'Reference preparation changed')
    for key,name in [('source_json','source.json'),('core','core.v'),('core_json','core.json'),
        ('harness','AdmissionScreen.sv'),('script','formal_screen.py'),('temporal_helper','temporal.py'),
        ('rom_helper','program_rom.py'),('rom_image','program.hex'),('screen_json','screen.json'),('aig','screen.aig')]:
        require(digest(directory/name)==record[key+'_sha256'],'Prepared artifact changed: '+name)
    require(record['source_json_sha256']==prior['source_json_sha256'] and record['core_json_sha256']==prior['core_json_sha256']
        and record['core_sha256']==prior['core_sha256'] and record['harness_sha256']==prior['harness_sha256'],
        'Native source/export or harness differs from frozen reference')
    require(digest(directory/'register_status_query_core.json')==prior['query_core_sha256'],
        'Pre-cube current graph differs from frozen48-premise reference')
    require(Path(record['query_core_path']).resolve()==directory/'reset_cube_query_core.json',
        'Unexpected combined query path')
    require(digest(directory/'reset_cube_query_core.json')==record['query_core_sha256'],'Combined query changed')
    for key,validator in [('native_word_domain_import',verify_words),('external_rom_domain_import',verify_rom),
        ('inactive_fu_import',verify_inactive),('register_status_import',verify_registers),('reset_cube_import',verify_cube)]:
        validator(record[key])
    for path,expected in cube['proof_dependencies_sha256'].items():
        require(record['native_word_domain_import']['proof_dependencies_sha256'].get(path)==expected,
            'Cube transitive proof closure missing from prepared record')
    before=read(directory/'register_status_query_core.json')['modules']['datapath']
    after=read(directory/'reset_cube_query_core.json')['modules']['datapath']
    preserved=cube['composition']['existing_predicate_cells_preserved']
    require(len(preserved)==479 and all(before['cells'][n]==after['cells'][n] for n in preserved),
        'Existing479word/RD predicate cells changed')
    require(before['ports']==after['ports'],'Native or probe ports changed')
    counts={k:sum(c['type']=='$'+k for c in after['cells'].values()) for k in ('assert','assume','cover')}
    require(counts=={'assert':0,'assume':47,'cover':0},'Combined graph must retain47proved conclusions only')
    lowered=read(directory/'screen.json')['modules']['AdmissionScreen']
    require({k:sum(c['type']=='$'+k for c in lowered['cells'].values()) for k in ('assert','assume','cover')}==record['query_property_counts'],
        'Actual lowered property inventory differs')
    require(not any(b in ('x','z') for c in lowered['cells'].values() for bs in c['connections'].values() for b in bs),
        'Literal undefined value in final model')
    with (directory/'screen.aig').open('rb') as stream:header=stream.readline().decode().split()
    require(header==record['aig_header'] and header[0]=='aig' and int(header[4])==0 and int(header[6])==3 and int(header[7])==48,
        'AIG property inventory differs')
    return record
