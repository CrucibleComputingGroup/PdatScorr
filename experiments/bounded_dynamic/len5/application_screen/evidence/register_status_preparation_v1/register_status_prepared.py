"""Strict read-only validation of the new48-premise preparation family.

Existing solver entry points retain their original8-premise guards. This
validator authorizes no backend run and does not weaken those guards.
"""
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE.parents[3]),str(HERE)]

from domain_lemmas import verify_dependencies as verify_words
from inactive_fu_import import verify_dependencies as verify_inactive
from register_status_import import verify_dependencies as verify_registers
from register_status_lemmas import digest,read,require
from rom_domain_import import verify_dependencies as verify_rom


def validate_register_status_prepared(directory):
    directory=Path(directory).resolve();record=read(directory/'summary.json')
    require(record['status']=='prepared_query_only' and record['accepted_optimization'] is False
        and record['engine']=='prepare','Only a completed preparation is eligible')
    require(record['abstraction_mode']=='none' and record['datapath_abstraction'] is None,'Native arithmetic required')
    require(record['native_hardware_contains_formal_properties'] is False,'Native hardware must be separate')
    require(record['query_property_counts']=={'assert':3,'assume':48,'cover':0},'Unexpected final property inventory')
    facts=record['register_status_import']
    require(facts['status']=='forty_rd_domains_and_register_status_facts_imported'
        and facts['derived_assumptions_added']==40 and facts['proved_reset_bits_substituted']==275
        and facts['new_unproved_internal_premises']==0 and facts['new_environmental_premises']==[]
        and facts['rf_candidate_substituted'] is False,'Unqualified register-status/RD composition')
    for key,name in [('source_json','source.json'),('core','core.v'),('core_json','core.json'),
        ('harness','AdmissionScreen.sv'),('script','formal_screen.py'),('temporal_helper','temporal.py'),
        ('rom_helper','program_rom.py'),('rom_image','program.hex'),('screen_json','screen.json'),('aig','screen.aig')]:
        require(digest(directory/name)==record[key+'_sha256'],'Prepared artifact changed: '+name)
    require(Path(record['query_core_path']).resolve()==directory/'register_status_query_core.json','Unexpected final query graph')
    require(digest(directory/'register_status_query_core.json')==record['query_core_sha256'],'Query graph changed')
    verify_words(record['native_word_domain_import']);verify_rom(record['external_rom_domain_import'])
    verify_inactive(record['inactive_fu_import']);verify_registers(facts)
    for path,expected in facts['proof_dependencies_sha256'].items():
        require(record['native_word_domain_import']['proof_dependencies_sha256'].get(path)==expected,
                'Register-status transitive closure missing from the prepared record')
    query=read(directory/'register_status_query_core.json')['modules']['datapath']
    counts={kind:sum(c['type']=='$'+kind for c in query['cells'].values()) for kind in ('assert','assume','cover')}
    require(counts=={'assert':0,'assume':47,'cover':0},'Query must contain7word+40RD conclusions only')
    lowered=read(directory/'screen.json')['modules']['AdmissionScreen']
    require({k:sum(c['type']=='$'+k for c in lowered['cells'].values()) for k in ('assert','assume','cover')}==record['query_property_counts'],
            'Actual lowered property counts differ')
    require(not any(b in ('x','z') for c in lowered['cells'].values() for bs in c['connections'].values() for b in bs),
            'Literal undefined value in final proof model')
    with (directory/'screen.aig').open('rb') as stream:header=stream.readline().decode().split()
    require(header==record['aig_header'] and header[0]=='aig' and int(header[4])==0 and int(header[6])==3 and int(header[7])==48,
            'Exported AIG property inventory differs')
    return record
