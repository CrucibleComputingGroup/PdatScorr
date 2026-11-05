"""Independent solver-free reset-cube semantics and frozen-artifact review."""
import copy
import hashlib
import itertools
import json
from pathlib import Path
import sys
import pytest

ROOT=Path(__file__).resolve().parents[2]
APP=ROOT/'experiments/bounded_dynamic/len5/application_screen'
sys.path.insert(0,str(APP))
import reset_cube

BUILD=Path('/home/allenjin/Projects/DAC_pscorr/experiments/bounded_dynamic/len5/build')
RUN=BUILD/'reset_cube_native_fixedpoint_v1'


def read(path):return json.loads(path.read_text())
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def tiny(kind,reset_polarity,enable_polarity):
    connections={'CLK':[2],'D':[4],'Q':[6]}
    parameters={'CLK_POLARITY':1,'WIDTH':1}
    if kind.startswith('$ald'):
        connections.update(ALOAD=[3],AD=['0']);parameters['ALOAD_POLARITY']=reset_polarity
    else:
        connections['ARST']=[3];parameters.update(ARST_POLARITY=reset_polarity,ARST_VALUE='0')
    if kind.endswith('e'):
        connections['EN']=[5];parameters['EN_POLARITY']=enable_polarity
    cell={'type':kind,'parameters':parameters,'attributes':{},'hide_name':0,'connections':connections,
        'port_directions':{p:'output' if p=='Q' else 'input' for p in connections}}
    return {'modules':{'toy':{'attributes':{},'ports':{n:{'direction':'input','bits':[b]}
        for n,b in [('clk_i',2),('rst_ni',3),('d',4),('en',5)]},'netnames':{},'cells':{'word':cell}}}}


def evaluate(projected,assignments):
    values=dict(assignments)
    def bits(items):return [values[x] if type(x)is int else int(x) for x in items]
    for cell in projected['modules']['ResetCube']['cells'].values():
        c=cell['connections'];kind=cell['type']
        if kind=='$mux':result=bits(c['B'] if bits(c['S'])[0] else c['A'])
        elif kind=='$ne':result=[int(bits(c['A'])!=bits(c['B']))]
        elif kind=='$reduce_or':result=[int(any(bits(c['A'])))]
        else:raise AssertionError('Unexpected toy combinational primitive '+kind)
        values.update(zip(c['Y'],result))
    return bits(projected['modules']['ResetCube']['ports']['cube_bad']['bits'])[0]


@pytest.mark.parametrize('kind,rp,ep',list(itertools.product(['$adff','$aldff','$adffe','$aldffe'],[0,1],[0,1])))
def test_adapter_truth_table_preserves_reset_priority_enable_and_current_state(kind,rp,ep):
    design=tiny(kind,rp,ep);rows,_=reset_cube.eligibility(design,'toy',reset_polarity=rp)
    for mode in ['base','induction']:
        projected,audit=reset_cube.project(design,'toy',rows,mode=mode)
        for rst,en,d,q in itertools.product([0,1],repeat=4):
            normal=q if mode=='base' else (d if not kind.endswith('e') or en==ep else 0)
            expected=0 if rst==rp else normal
            assert evaluate(projected,{2:0,3:rst,4:d,5:en,6:q})==expected
        assert audit['reset_base_premise']==({'rst_ni':rp} if mode=='base' else None)


def test_noncandidate_state_is_free_while_joint_hypothesis_is_only_selected_q():
    design=tiny('$aldff',0,1);m=design['modules']['toy']
    m['cells']['other']=copy.deepcopy(m['cells']['word']);m['cells']['other']['connections']['Q']=[7]
    m['cells']['word']['connections']['D']=[7]
    selected=[r for r in reset_cube.eligibility(design,'toy')[0] if r['name']=='word']
    projection,audit=reset_cube.project(design,'toy',selected)
    assert audit['hypothesis_q_constants']=={6:'0'}
    assert audit['arbitrary_other_state_outputs']==[{'native_cell':'other','native_port':'Q','bits':[7],'port':'free_state_0'}]
    assert evaluate(projection,{2:0,3:1,4:0,5:0,7:0})==0
    assert evaluate(projection,{2:0,3:1,4:0,5:0,7:1})==1


@pytest.fixture(scope='module')
def frozen():
    if not (RUN/'summary.json').is_file():pytest.skip('Original reset-cube artifacts unavailable')
    summary=read(RUN/'summary.json');source=read(RUN/'source.json');rows=read(RUN/'selected_words.json')
    assert summary['status']=='reset_cube_certified_query_patch_only' and summary['query_only'] and not summary['accepted_optimization']
    assert not summary['new_environmental_premises']
    assert sha(RUN/'source.json')==summary['source_sha256']=='bb52d686f974809e0bebd4e2b373414ec9a53af34cff5a6a48d1e5ab2465307b'
    for path,expected in summary['dependencies_sha256'].items():assert sha(Path(path))==expected
    assert sha(APP/'reset_cube.py')==sha(RUN/'reset_cube.py')
    assert sha(APP/'reset_cube_fixedpoint.py')==sha(RUN/'reset_cube_fixedpoint.py')
    return summary,source,rows


def test_native_selected_words_and_fixedpoint_are_reconstructible(frozen):
    summary,source,rows=frozen;eligible,audit=reset_cube.eligibility(source,'datapath')
    assert audit==summary['eligibility']
    current=eligible
    for index,record in enumerate(summary['rounds']):
        assert record['index']==index and record['candidate_words']==len(current)
        assert record['candidate_bits']==sum(r['width'] for r in current)
        constants=record['cofactor']['initial_cofactor_output_constants']
        lower=read(RUN/f'round_{index}/lowered.json')['modules']['ResetCube']
        observations=read(RUN/f'round_{index}/projection_audit.json')['observations']
        assert constants=={item['candidate']:lower['ports'][item['port']]['bits'][0] for item in observations}
        discarded=[r['name'] for r in current if constants[r['name']]!='0']
        assert discarded==record['discarded_words']
        current=[r for r in current if constants[r['name']]=='0']
        assert len(current)==record['kept_words']
    assert current==rows and len(rows)==42 and sum(r['width'] for r in rows)==583
    assert not summary['rounds'][-1]['discarded_words']
    assert all(r['cell']['type']=='$aldff' and r['reset_value']==['0']*r['width'] for r in rows)


@pytest.mark.parametrize('mode',['induction','base'])
def test_actual_projection_and_symbolic_choices_preserve_source_semantics(frozen,mode):
    summary,source,rows=frozen;directory=RUN/('final_'+mode);proof=summary['final_proofs'][mode]
    projected,audit=reset_cube.project(source,'datapath',rows,mode=mode)
    assert projected==read(directory/'projection.json')
    assert json.loads(json.dumps(audit))==read(directory/'projection_audit.json')
    assert sha(directory/'projection.json')==proof['projection_sha256']
    assert audit['hypothesis_q_constants']==({b:'0' for r in rows for b in r['q']} if mode=='induction' else {})
    original=source['modules']['datapath'];cut_bits={b for c in audit['arbitrary_other_state_outputs'] for b in c['bits']}
    all_state={b for c in original['cells'].values() if reset_cube.state_cell(c) for pin,bs in c['connections'].items()
        if c['port_directions'][pin]=='output' for b in bs}
    assert cut_bits==all_state-set(audit['hypothesis_q_constants'])
    # Independently check that choice exposure deletes only symbolic drivers,
    # preserving exact output IDs as unrestricted input bits.
    for before,after in [('symbolized_before_prep.json','binary_inputs_before_prep.json'),('normalized_symbolic.json','lowered.json')]:
        a=read(directory/before)['modules']['ResetCube'];b=read(directory/after)['modules']['ResetCube']
        removed={n for n,c in a['cells'].items() if c['type'] in ('$anyseq','$anyconst')}
        assert set(b['cells'])==set(a['cells'])-removed
        assert all(b['cells'][n]==c for n,c in a['cells'].items() if n not in removed)
        assert all(b['ports'][n]==p for n,p in a['ports'].items())
        added=[p for n,p in b['ports'].items() if n not in a['ports']]
        assert all(p['direction']=='input' for p in added)
        assert sorted(tuple(p['bits']) for p in added)==sorted(tuple(a['cells'][n]['connections']['Y']) for n in removed)
    lower=read(directory/'lowered.json')['modules']['ResetCube']
    assert not any(reset_cube.state_cell(c) or c['type'] in reset_cube.FORBIDDEN for c in lower['cells'].values())
    assert not any(b in ('x','z') for c in lower['cells'].values() for bs in c['connections'].values() for b in bs)
    assert sha(directory/'lowered.json')==proof['lowered_sha256']


@pytest.mark.parametrize('mode',['induction','base'])
def test_joint_sat_certificates_have_only_intended_reset_premise(frozen,mode):
    summary,_,_=frozen;directory=RUN/('final_'+mode);proof=summary['final_proofs'][mode]
    for field,subdir in [('symbolize_execution','symbolize'),('execution','execution'),('sat_execution','sat_execution')]:
        result=proof[field];assert result['returncode']==0 and not result['timeout']
        assert sha(directory/subdir/'run.ys')==result['script_sha256']
        assert sha(directory/subdir/'run.log')==result['log_sha256']
    script=(directory/'sat_execution/run.ys').read_text()
    assert '-prove cube_bad 0' in script and '-set-def-inputs' in script
    assert ('-set rst_ni 0' in script)==(mode=='base')
    assert script.count(' -set ')==(1 if mode=='base' else 0)
    assert '-set-assumes' not in script
    log=(directory/'sat.log').read_text()
    assert sha(directory/'sat.log')==proof['sat_log_sha256']
    assert 'SAT proof finished - no model found: SUCCESS!' in log
    assert 'SAT proof finished - model found: FAIL!' not in log


def test_wholegraph_patch_changes_only_selected_583_q_bits(frozen):
    summary,source,rows=frozen;patch=read(RUN/'patch.json');changed={int(k):v for k,v in patch['constant_substitutions'].items()}
    assert changed=={b:v for r in rows for b,v in zip(r['q'],r['reset_value'])}
    assert len(changed)==583 and set(changed.values())=={'0'}
    modified=read(RUN/'query_only_patch.json');assert sha(RUN/'query_only_patch.json')==summary['query_only_patch_sha256']
    a=source['modules']['datapath'];b=modified['modules']['datapath']
    assert set(a['cells'])-set(b['cells'])=={r['name'] for r in rows}==set(patch['removed_whole_ff_cells'])
    assert not set(b['cells'])-set(a['cells'])
    for name,cell in b['cells'].items():
        expected=copy.deepcopy(a['cells'][name])
        for pin,bs in expected['connections'].items():
            if expected['port_directions'][pin]=='input':expected['connections'][pin]=[changed.get(x,x) for x in bs]
        assert cell==expected
    for kind in ['ports','netnames']:
        assert set(a[kind])==set(b[kind])
        for name,item in a[kind].items():assert b[kind][name]==dict(item,bits=[changed.get(x,x) for x in item['bits']])
    assert all(a['ports'][n]==b['ports'][n] for n,p in a['ports'].items() if p['direction']=='input')
    assert {k:v for k,v in a.items() if k not in ['cells','ports','netnames']}=={k:v for k,v in b.items() if k not in ['cells','ports','netnames']}
