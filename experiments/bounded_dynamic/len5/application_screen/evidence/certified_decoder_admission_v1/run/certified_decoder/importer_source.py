"""Import a source-bound decoder substitution only after replaying its certificate.

This adds no formal assumptions. The actual zero-fault instruction ROM and
native initial reset must imply the certificate's external instruction domain.
"""
from __future__ import annotations
import copy
import json
from pathlib import Path
import re
import sys

from odc.temporal import digest, run_command

PREMISES = [
    'initial rst_ni == 0',
    '(rst_ni && instr_rvalid_i) -> instruction response word in declared domain',
]
OUTPUTS = {'issue_type_o':4,'except_code_o':5,'assigned_eu_o':3,'skip_eu_o':1,
    'eu_ctl_o':4,'mem_crit_o':1,'order_crit_o':1,'rs1_req_o':1,'rs1_is_pc_o':1,
    'rs2_req_o':1,'rs2_is_imm_o':1,'rd_upd_o':1,'imm_format_o':3}


def exact_alphabet(expression):
    """Parse only a disjunction of exact 32-bit word equalities; never eval."""
    result=set()
    for term in expression.split('||'):
        match=re.fullmatch(r"\s*\(\s*instruction_i\s*==\s*(0|32'h[0-9a-fA-F]{8})\s*\)\s*",term)
        if not match:
            raise ValueError('Certificate domain is not a strict exact-word alphabet')
        value=0 if match[1]=='0' else int(match[1][4:],16)
        if value in result:
            raise ValueError('Duplicate exact-word domain term')
        result.add(value)
    if not result or 0 not in result:
        raise ValueError('Certificate domain must contain the reset/bubble/fault zero word')
    return result


def validate_contract(certificate, image, *, zero_fault_data, initial_reset):
    if certificate.get('status')!='component_equivalence_and_domain_propagation_certified':
        raise ValueError('Certificate is withdrawn or not certified')
    if certificate.get('domain')!='program_alphabet' or certificate.get('external_premises')!=PREMISES:
        raise ValueError('Expected exact-alphabet certificate with reset-qualified response premise')
    required_true=('all_decoder_external_consumers_observed','native_ports_and_all_unmodified_cells_preserved',
                   'domain_projection_cells_unchanged_by_specialization')
    if any(certificate.get(name) is not True for name in required_true):
        raise ValueError('Certificate lacks complete decoder substitution closure')
    required_false=('invalid_instruction_payload_restricted','instruction_payload_during_reset_restricted',
                    'physical_candidate_has_formal_monitors')
    if any(certificate.get(name) is not False for name in required_false):
        raise ValueError('Unsupported certificate payload restriction or formal hardware')
    if (certificate.get('decoder_outputs')!=OUTPUTS or certificate.get('timing_or_occupancy_premises')!=[]
        or certificate.get('unobserved_external_consumers')!=[] or certificate.get('original_state_cell_drivers_replaced')!=0):
        raise ValueError('Unsupported observation, timing, or state substitution scope')
    if not initial_reset or not zero_fault_data or image is None:
        raise ValueError('Certified import requires native initial reset and a zero-fault immutable ROM')
    if image.get('immutable_instruction_image') is not True or image.get('byte_order')!='little':
        raise ValueError('Unsupported instruction platform')
    words=image.get('words',{})
    if not words or set(words)!=set(range(0,image['bytes'],4)):
        raise ValueError('ROM words must cover the complete aligned instruction image')
    allowed=exact_alphabet(certificate['domain_expression'])
    if any(type(value) is not int or not 0<=value<2**32 for value in words.values()):
        raise ValueError('ROM word is not a defined 32-bit integer')
    if not set(words.values())|{0} <= allowed:
        raise ValueError('ROM contains a word outside the certified alphabet')
    return allowed


def import_decoder(certificate_path, original_path, image, directory, *, certifier,
                   zero_fault_data=False, initial_reset=False, timeout=30):
    certificate_path,original_path,certifier=map(lambda p:Path(p).resolve(),
                                                (certificate_path,original_path,certifier))
    certificate=json.loads(certificate_path.read_text())
    allowed=validate_contract(certificate,image,zero_fault_data=zero_fault_data,initial_reset=initial_reset)
    if digest(certifier)!=certificate['certifier_sha256']:
        raise ValueError('Certificate verifier implementation hash changed')
    if digest(original_path)!=certificate['native_original_sha256']:
        raise ValueError('Fresh native source does not match certificate original hash')
    native_candidate=Path(certificate['native_candidate_json']).resolve()
    if digest(native_candidate)!=certificate['native_candidate_sha256']:
        raise ValueError('Certified native candidate hash changed')
    prepared=Path(certificate['native_original_json']).resolve().parent
    candidate=Path(certificate['candidate_summary']).resolve().parent
    domain=Path(certificate['domain_summary']).resolve().parent
    paired=Path(certificate['paired_proof_summary']).resolve().parent
    if native_candidate.parent!=candidate:
        raise ValueError('Candidate source and proof-directory bindings disagree')
    directory=Path(directory).resolve();directory.mkdir()
    (directory/'certificate.json').write_bytes(certificate_path.read_bytes())
    (directory/'certifier_source.py').write_bytes(certifier.read_bytes())
    (directory/'importer_source.py').write_bytes(Path(__file__).read_bytes())
    fresh=directory/'revalidated_certificate.json'
    argv=[sys.executable,str(certifier),'--prepared',str(prepared),'--candidate',str(candidate),
          '--domain-proof',str(domain),'--pair-recheck',str(paired),'--output',str(fresh)]
    execution=run_command(argv,directory/'certificate_recheck.log',timeout)
    if execution['returncode'] or execution['timeout'] or not fresh.exists():
        raise ValueError('Certificate verifier replay failed')
    if json.loads(fresh.read_text())!=certificate:
        raise ValueError('Fresh certificate differs from the supplied certificate')
    original=json.loads(original_path.read_text())
    modified=json.loads(native_candidate.read_text())
    if set(original['modules'])!={'datapath'} or set(modified['modules'])!={'datapath'}:
        raise ValueError('Expected flattened native datapath modules')
    a,b=original['modules']['datapath'],modified['modules']['datapath']
    if a['ports']!=b['ports'] or a['netnames']!=b['netnames'] or set(a['cells'])!=set(b['cells']):
        raise ValueError('Native ports, aliases, or cell set changed outside substitution')
    changed={n for n in a['cells'] if a['cells'][n]!=b['cells'][n]}
    if changed!=set(certificate['changed_cells']):
        raise ValueError('Candidate changed cells disagree with certified substitution')
    for name in changed:
        if any(token in a['cells'][name]['type'].lower() for token in ('ff','latch','mem')):
            raise ValueError('Certified decoder import may not replace native storage')
    if any(c['type'] in ('$assume','$assert','$check','$cover','$anyseq','$anyconst') for c in b['cells'].values()):
        raise ValueError('Candidate contains formal hardware')
    (directory/'native_candidate.json').write_bytes(native_candidate.read_bytes())
    record={'status':'certificate_replayed_and_native_substitution_bound','assumptions_added':0,
        'certificate_sha256':digest(certificate_path),'certificate_path':str(certificate_path),
        'certifier_sha256':digest(certifier),'certifier_path':str(certifier),
        'importer_sha256':digest(Path(__file__)),'fresh_certificate_sha256':digest(fresh),
        'original_native_sha256':digest(original_path),'candidate_native_sha256':digest(native_candidate),
        'native_candidate_path':str(native_candidate),'verifier_execution':execution,
        'certified_alphabet':[f'{v:08x}' for v in sorted(allowed)],
        'rom_words':[f'{v:08x}' for v in sorted(set(image['words'].values()))],
        'rom_image_sha256':image['image_sha256'],'fault_payload':0,
        'initial_reset_required':True,'instruction_premise_reset_qualified':True,
        'changed_cells':sorted(changed),'native_storage_drivers_replaced':0,
        'composition':'ROM returns only certified words or zero; synchronous initial reset establishes both response stages, and stall/flush transitions preserve that domain after reset. No instruction-domain assumption is inserted into the admission query.'}
    (directory/'summary.json').write_text(json.dumps(record,indent=2)+'\n')
    return copy.deepcopy(modified),record
