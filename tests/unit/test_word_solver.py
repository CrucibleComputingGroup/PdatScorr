"""Fail-closed status parsing and retained word-level backend regressions."""
import importlib.util
import json
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
APP = ROOT/'experiments/bounded_dynamic/len5/application_screen'
spec = importlib.util.spec_from_file_location('word_solver',APP/'word_solver.py')
module = importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
EVIDENCE = APP/'evidence/word_solver_validation_v3'
GOOD = """INVARCHECK: init |= inv...OK
INVARCHECK: inv & trans |= inv'...OK
INVARCHECK: inv |= prop...OK
Invariant Check PASSED
unsat
b0
"""


def test_explicit_ic3_unsat_requires_all_invariant_checks():
    run={'returncode':1,'timeout':False}
    assert module.classify(run,GOOD)=='proved_safety_query_only'
    for token in ['Invariant Check PASSED', 'init |= inv...OK', "inv & trans |= inv'...OK", 'inv |= prop...OK']:
        assert module.classify(run,GOOD.replace(token,''))=='unknown_or_error'


@pytest.mark.parametrize('edit', ['timeout','wrong_exit','bounded_unsat','extra_status','solver_error'])
def test_ambiguous_or_partial_results_never_prove(edit):
    run={'returncode':1,'timeout':False};text=GOOD
    if edit=='timeout':run['timeout']=True
    elif edit=='wrong_exit':run['returncode']=0
    elif edit=='bounded_unsat':text='unsat\nb0\n'
    elif edit=='extra_status':text+='unknown\n'
    else:text+='error\n'
    assert module.classify(run,text)!='proved_safety_query_only'


def test_multiple_properties_and_constraints_survive_export():
    record=json.loads((EVIDENCE/'three_asserts_eight_constraints_positive/summary.json').read_text())
    assert record['property_counts']=={'assert':3,'assume':8,'cover':0}
    inv=module.btor_inventory(EVIDENCE/'three_asserts_eight_constraints_positive/model.btor2')
    assert inv['bad']==1 and inv['constraint']==8
    negative=json.loads((EVIDENCE/'third_assertion_negative/summary.json').read_text())
    assert negative['status']=='counterexample_in_query_model'
    assert negative['witness_check']['returncode']==0


def test_initial_state_and_symbolic_choice_regressions_are_real_counterexamples():
    for name in ['nonzero_initial_value_negative','uninitialized_state_negative',
                 'symbolic_x_negative','changing_anyseq_negative','initial_reset_not_permanent_negative']:
        record=json.loads((EVIDENCE/name/'summary.json').read_text())
        assert record['status']=='counterexample_in_query_model'
        assert record['negative_bmc']['returncode']==0 and not record['negative_bmc']['timeout']
        assert record['witness_check']['returncode']==0 and not record['witness_check']['timeout']
        assert module.digest(EVIDENCE/name/'counterexample.wit')==record['witness_sha256']
    nonzero=module.btor_inventory(EVIDENCE/'nonzero_initial_value_negative/model.btor2')
    uninit=module.btor_inventory(EVIDENCE/'uninitialized_state_negative/model.btor2')
    assert nonzero['state_bits']==4 and len(nonzero['initializers'])==1
    assert uninit['state_bits']==4 and uninit['initializers']==[]


def test_dependency_change_is_rejected(tmp_path):
    p=tmp_path/'model';p.write_text('native')
    hashes={str(p):module.digest(p)}
    module.verify_dependencies(hashes)
    p.write_text('changed')
    with pytest.raises(ValueError,match='Dependency changed'):
        module.verify_dependencies(hashes)


def test_temporal_anyseq_changes_but_anyconst_proves_stable():
    paired=json.loads((APP/'evidence/word_solver_choices_v2/summary.json').read_text())
    assert paired['status']=='paired_anyseq_anyconst_semantics_validated'
    before,after=paired['anyseq_values'][:2]
    assert before['frame']==0 and after['frame']==1 and before['bits']!=after['bits']
    assert [test['status'] for test in paired['records']]==[
        'counterexample_in_query_model','proved_safety_query_only']
    assert paired['records'][0]['witness_check']['returncode']==0
