import copy
import importlib.util
import json
from pathlib import Path

import pytest

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('inactive_independent_audit',HERE/'audit.py')
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
EVIDENCE=HERE.parents[1]/'evidence/inactive_fu_lemmas_v1'

@pytest.fixture
def native_ff():
    design=json.loads((EVIDENCE/'mul_row_0/projection.json').read_text())['modules']['NativeRow']
    return copy.deepcopy(next(cell for cell in design['cells'].values() if cell['type']=='$aldff'))

@pytest.mark.parametrize('mutation',['reset_polarity','clock','reset_pin','reset_value'])
def test_changed_native_reset_boundary_is_rejected(native_ff,mutation):
    if mutation=='reset_polarity':native_ff['parameters']['ALOAD_POLARITY']='1'
    elif mutation=='clock':native_ff['connections']['CLK']=[999]
    elif mutation=='reset_pin':native_ff['connections']['ALOAD']=[999]
    else:native_ff['connections']['AD'][0]='1'
    with pytest.raises(AssertionError):module.slice_aldff(native_ff,[0])

def test_duplicate_driver_is_rejected(native_ff):
    with pytest.raises(AssertionError):module.drivers({'cells':{'first':native_ff,'second':copy.deepcopy(native_ff)}})

def test_negative_witnesses_have_admission_and_real_failure_not_terminal_marker():
    for bank in ('mul','div'):
        for row in range(4):
            rows=module.vcd_rows(EVIDENCE/f'{bank}_row_{row}'/'negative/counterexample.vcd')
            assert rows[0]['rst_ni']==0 and rows[0]['row_q']==0
            assert any(r['rst_ni'] and r['insert_i'] and r['new_index_i']==row for r in rows)
            assert any(r['row_q']!=0 for r in rows)
            assert [r['smt_step'] for r in rows]==[0,1,2]
