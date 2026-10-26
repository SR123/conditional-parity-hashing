#!/usr/bin/env python3
"""Independent direct-marginal audit. Python standard library only.

No import from the circulated checker. Rational intervals enclose each
entropy computed from the atom probabilities, before checking closed formulas.
The ln series follows the elementary identity 2 atanh((x-1)/(x+1)).
"""
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
from pathlib import Path
from decimal import Decimal, localcontext
import json

ROOT = Path(__file__).resolve().parent
P, Q, T = [F(i, 10**8) for i in (74830195, 22122546, 3047259)]
ROWS = '''0000 0210 0011
0101 0321 0120
1010 1100 1002
1212 1332 1230
2121 2001 2103
2323 2233 2331
3232 3012 3213
3333 3123 3322'''
LAW = {tuple(map(int, atom)): w/8 for row in ROWS.splitlines()
       for atom, w in zip(row.split(), (P,Q,T))}
assert len(LAW) == 24 and sum(LAW.values()) == 1

def add(a,b): return (a[0]+b[0], a[1]+b[1])
def scale(c,a): return (c*a[0],c*a[1]) if c >= 0 else (c*a[1],c*a[0])
def sub(a,b): return add(a,scale(-1,b))
def divide(a,b):
    assert b[0] > 0
    vals=[x/y for x in a for y in b]
    return min(vals), max(vals)

@lru_cache(None)
def ln_unit(x):
    assert 1 <= x <= 2
    t=(x-1)/(x+1); power=t; partial=F(0)
    terms=64
    for i in range(terms):
        partial += 2*power/(2*i+1); power *= t*t
    return partial, partial+2*power/((2*terms+1)*(1-t*t))

@lru_cache(None)
def log2(x):
    assert x > 0
    e=0
    while x < 1: x*=2; e-=1
    while x >= 2: x/=2; e+=1
    v=divide(ln_unit(x),ln_unit(F(2)))
    return v[0]+e,v[1]+e

def entropy(probs):
    out=(F(0),F(0))
    for p in probs:
        if p: out=add(out,scale(-p,log2(p)))
    return out

def marginal(f):
    d=defaultdict(F)
    for atom,p in LAW.items():d[f(atom)]+=p
    return dict(d)

def H(f):return entropy(marginal(f).values())
def projection(atom,S):return tuple(atom[i] for i in range(4) if S & (1<<i))
def hb(p):return entropy([p,1-p])
chi=lambda x: int(x in (1,2))
U=lambda x:chi(x[0]); V=lambda x:chi(x[1]); E=lambda x:chi(x[0])^chi(x[2])
for a in LAW:
    assert (chi(a[0])^chi(a[1])^chi(a[2])^chi(a[3]))==0
    assert (chi(a[2]),chi(a[3]))==(U(a)^E(a),V(a)^E(a))
for i,j in [(0,1),(1,0),(2,3),(3,2)]:
    assert set(marginal(lambda a:(a[i],chi(a[j]))).values())=={F(1,8)}

source={S:H(lambda a,S=S:projection(a,S)) for S in range(16)}
calH=entropy((P,Q,T))
three=(F(3),F(3))
formulas={1:(F(2),F(2)),2:(F(2),F(2)),4:(F(2),F(2)),8:(F(2),F(2)),
          3:add(three,hb(Q)),5:add((3-P,3-P),hb(P)),9:three,6:three,
          10:add((3-P,3-P),hb(P)),12:add(three,hb(T))}
formulas.update({S:add(three,calH) for S in range(16) if S.bit_count()>=3})
for S,v in formulas.items():
    d=sub(source[S],v)
    assert d[0] <= 0 <= d[1] and d[1]-d[0]<F(1,10**50)
    if S.bit_count()>=3:assert len(marginal(lambda a:projection(a,S)))==24

b=sub(source[15],source[3])
target={S:sub(source[S],scale(min(3,S.bit_count()),b)) for S in source}

def J(h,a,b,c,d):
    # Direct expansion of I(C;D|A)+I(C;D|B)+I(A;B)-I(C;D).
    masks=[(1<<a)|(1<<c),(1<<a)|(1<<d),(1<<b)|(1<<c),
           (1<<b)|(1<<d),(1<<c)|(1<<d)]
    out=(F(0),F(0))
    for S in masks:out=add(out,h[S])
    for S in [(1<<c),(1<<d),(1<<a)|(1<<b),
              (1<<a)|(1<<c)|(1<<d),(1<<b)|(1<<c)|(1<<d)]:out=sub(out,h[S])
    return out

js=J(source,0,1,2,3);jz=J(target,0,1,2,3)
same=sub(js,jz);assert same[0] <= 0 <= same[1]
score=divide(jz,target[15])
assert -F(97387436923,10**12)<=score[0]<=score[1]<=-F(97387436922,10**12)
R=F(371,2000);assert R<b[0]
interior={S:sub(source[S],(R*min(3,S.bit_count()),)*2) for S in source}
scoreR=divide(J(interior,0,1,2,3),interior[15]);assert scoreR[1]<-F(9738,10**5)
cross_margin=add(J(interior,0,1,2,3),scale(F(9738,10**5),interior[15]))
assert cross_margin[1] < -F(1,250000)

missing=[(3,E),(5,V),(9,V),(6,U),(10,U),(12,U)]
thresholds={S:sub(H(lambda a,S=S,f=f:(projection(a,S),f(a))),source[S]) for S,f in missing}
assert sub(thresholds[3],b)[0]<=0<=sub(thresholds[3],b)[1]
for S,v in thresholds.items():
    if S!=3:assert v[0]>b[1]

def txt(q):
    with localcontext() as ctx:
        ctx.prec=65
        return str(Decimal(q.numerator)/Decimal(q.denominator))
def interval(v):
    # Compact, outward-rounded rational endpoints; calculations above are exact.
    den=10**55
    lo=(v[0]*den).__floor__(); hi=(v[1]*den).__ceil__()
    return {'lower':str(F(lo,den)),'upper':str(F(hi,den)),
            'mid_decimal':txt(sum(v)/2)}
orientations={}
for a,bv in combinations(range(4),2):
    c,d=[i for i in range(4) if i not in (a,bv)]
    val=J(target,a,bv,c,d)
    orientations['ABCD'[a]+'ABCD'[bv]]=interval(divide(val,target[15]))
    if (a,bv)!=(0,1):assert val[0]>0
out={'status':'PASS','method':'independent exact rational marginal accumulation and log enclosures',
     'parameters':list(map(str,(P,Q,T))),'atoms':len(LAW),
     'source':{str(S):interval(v) for S,v in source.items() if S},
     'target':{str(S):interval(v) for S,v in target.items() if S},
     'b':interval(b),'J':interval(jz),'score':interval(score),
     'all_six_signed_scores':orientations,'pair_thresholds':{str(S):interval(v) for S,v in thresholds.items()},
     'interior_rate':str(R),'interior_score':interval(scoreR),
     'interior_threshold_cross_margin':interval(cross_margin),
     'scope':'Finite source algebra and numerical bounds only; membership proved separately.'}
(ROOT/'independent_source_audit.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: exact source, 15 marginal entropies, bit identities, six thresholds and six scores.')
for label,val in [('b',b),('J',jz),('z(N)',target[15]),('signed endpoint score',score),('signed R=.1855 score',scoreR)]:
    print(label,txt(sum(val)/2))
