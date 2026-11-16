"""Development utility: populate examples with documented valid/invalid proofs."""
import json
from pathlib import Path
from Component_1.formula import Atom, Not, And, Imp, Iff, Next, Always, Eventually, Until, to_dict
from Component_1.axioms import axiom_instance
p, q = Atom(0), Atom(1)
OUT = Path(__file__).parent / 'examples'
OUT.mkdir(exist_ok=True)

def line(f, rule, params=(), refs=()):
    d = {'formula':to_dict(f),'rule':rule}
    if params: d['params'] = [to_dict(x) for x in params]
    if refs: d['refs'] = list(refs)
    return d

def save(name, goal, lines, expected):
    (OUT / (name + '.json')).write_text(json.dumps({'goal':to_dict(goal),'lines':lines,
                                                    'expected_accept':expected},indent=2)+'\n')

w = Imp(p,p)
save('01_valid_r1', w, [line(w,'R1')], True)
save('02_valid_r3', Always(w), [line(w,'R1'),line(Always(w),'R3',refs=(0,))], True)
for i, ax in enumerate(('A1','A2','A3','A4','A5','A6','A7','A8'),start=3):
    params = (p,q) if ax in ('A2','A4','A7','A8') else (p,)
    f=axiom_instance(ax,params)
    save(f'{i:02}_valid_{ax.lower()}', f, [line(f,ax,params=params)], True)
con=Imp(w,Imp(q,w)); target=Imp(q,w)
save('11_valid_r2',target,[line(w,'R1'),line(con,'R1'),line(target,'R2',refs=(0,1))],True)
save('12_invalid_r1',Imp(p,Always(p)),[line(Imp(p,Always(p)),'R1')],False)
save('13_invalid_future_ref',Always(w),[line(w,'R1'),line(Always(w),'R3',refs=(1,))],False)
save('14_invalid_wrong_goal',p,[line(w,'R1')],False)
bad=Iff(Next(Not(p)),Not(Next(q)))
save('15_invalid_axiom_instantiation',bad,[line(bad,'A3',params=(p,))],False)
save('16_invalid_r2',p,[line(w,'R1'),line(con,'R1'),line(p,'R2',refs=(0,1))],False)
save('17_invalid_r3',Always(p),[line(w,'R1'),line(Always(p),'R3',refs=(0,))],False)
save('18_invalid_unknown_rule',w,[line(w,'R4')],False)
print('Generated',len(list(OUT.glob('*.json'))),'proof examples')
