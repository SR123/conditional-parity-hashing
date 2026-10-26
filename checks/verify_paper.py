#!/usr/bin/env python3
"""Exact finite checks and rational logarithm bounds for conditional_parity_hashing.tex.

Python >= 3.10, standard library only. No solver, floating-point arithmetic, or
external certificate is used. This checks the paper's finite source/formulas
and score enclosure. Almost-entropic membership follows from its written proof.
"""
from fractions import Fraction as F
from collections import defaultdict, Counter
from itertools import combinations
from pathlib import Path
import json

P,Q,T=map(lambda n:F(n,100000000),(74830195,22122546,3047259))
assert P+Q+T==1 and 0<T<Q<F(1,2)
rows=('0000 0210 0011','0101 0321 0120','1010 1100 1002','1212 1332 1230',
      '2121 2001 2103','2323 2233 2331','3232 3012 3213','3333 3123 3322')
law={tuple(map(int,a)):w/8 for row in rows for a,w in zip(row.split(),(P,Q,T))}
assert len(law)==24 and sum(law.values())==1
chi=(0,1,1,0)
def marginal(fn):
    pp=defaultdict(F)
    for a,p in law.items():pp[fn(a)]+=p
    return dict(pp)
def coords(a,S):return tuple(a[i] for i in range(4) if S>>i&1)
for i in range(4):assert Counter(marginal(lambda a,i=i:a[i]).values())==Counter({F(1,4):4})
for S in (7,11,13,14):assert len(marginal(lambda a,S=S:coords(a,S)))==24
for a in law:assert chi[a[0]]^chi[a[1]]^chi[a[2]]^chi[a[3]]==0
for i,j in ((0,1),(1,0),(2,3),(3,2)):
    pp=marginal(lambda a,i=i,j=j:(a[i],chi[a[j]]))
    assert len(pp)==8 and set(pp.values())=={F(1,8)}
assert marginal(lambda a:chi[a[0]]^chi[a[2]])=={0:P,1:Q+T}
forms=(1,2,5,6)
def rank(rr):
    span={0}
    for r in rr:span|={s^r for s in list(span)}
    return len(span).bit_length()-1
for S in range(1,16):assert rank([forms[i] for i in range(4) if S>>i&1])==min(3,S.bit_count())

# Exact multiplicity checks prove every source and completion entropy formula.
pair_masses={3:Counter({Q/8:8,(P+T)/8:8}),5:Counter({P/4:4,(Q+T)/8:8}),
             9:Counter({F(1,8):8}),6:Counter({F(1,8):8}),
             10:Counter({P/4:4,(Q+T)/8:8}),12:Counter({T/8:8,(P+Q)/8:8})}
missing={3:lambda a:chi[a[0]]^chi[a[2]],5:lambda a:chi[a[1]],9:lambda a:chi[a[1]],
         6:lambda a:chi[a[0]],10:lambda a:chi[a[0]],12:lambda a:chi[a[0]]}
for S,counts in pair_masses.items():
    assert Counter(marginal(lambda a,S=S:coords(a,S)).values())==counts
    pp=marginal(lambda a,S=S:(coords(a,S),missing[S](a)))
    expected=Counter({P/8:8,Q/8:8,T/8:8}) if S in (3,5,10,12) else Counter({P/8:8,(Q+T)/8:8})
    assert Counter(pp.values())==expected

class Interval:
    def __init__(self,lo,hi=None):self.lo=F(lo);self.hi=self.lo if hi is None else F(hi);assert self.lo<=self.hi
    def __add__(self,o):
        o=o if isinstance(o,Interval) else Interval(o)
        return Interval(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return Interval(-self.hi,-self.lo)
    def __sub__(self,o):return self+-o if isinstance(o,Interval) else self+(-F(o))
    def __rsub__(self,o):return -self+o
    def __mul__(self,o):
        o=o if isinstance(o,Interval) else Interval(o)
        pp=[a*b for a in (self.lo,self.hi) for b in (o.lo,o.hi)]
        return Interval(min(pp),max(pp))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=o if isinstance(o,Interval) else Interval(o)
        assert not(o.lo<=0<=o.hi)
        return self*Interval(min(1/o.lo,1/o.hi),max(1/o.lo,1/o.hi))
    def out(self,digits=12):
        scale=10**digits
        a=(self.lo*scale).__floor__();b=(self.hi*scale).__ceil__()
        def fixed(n):
            sign='-' if n<0 else '';n=abs(n)
            return sign+str(n//scale)+'.'+str(n%scale).zfill(digits)
        return [fixed(a),fixed(b)]

def ln_unit(q,terms=42):
    assert 1<=q<=2
    y=(q-1)/(q+1);yy=y*y;term=y;lo=F(0)
    for j in range(terms):lo+=2*term/(2*j+1);term*=yy
    return Interval(lo,lo+2*term/((2*terms+1)*(1-yy)))
LN2=ln_unit(F(2))
def log2(q):
    assert q>0
    k=0;r=q
    while r<1:r*=2;k-=1
    while r>=2:r/=2;k+=1
    return ln_unit(r)/LN2+k

def entropy(pp):return sum((-p*log2(p) for p in pp if p),Interval(0))
def hb(p):return entropy((p,1-p))
HH=entropy((P,Q,T));a,c,d=hb(P),hb(Q),hb(T)
bb=HH-c
h=[Interval(0)]
for S in range(1,16):h.append(entropy(marginal(lambda at,S=S:coords(at,S)).values()))
formulas={1:Interval(2),2:Interval(2),4:Interval(2),8:Interval(2),3:3+c,
          5:3-P+a,10:3-P+a,9:Interval(3),6:Interval(3),12:3+d}
formulas.update({S:3+HH for S in (7,11,13,14,15)})
for S in range(1,16):assert h[S].lo<=formulas[S].hi and formulas[S].lo<=h[S].hi
z=[h[S]-min(3,S.bit_count())*bb for S in range(16)]
j=2-2*P+2*a+d-2*HH-c
den=3-2*HH+3*c
def ingleton(v):
    return ((v[5]+v[9]-v[1]-v[13])+(v[6]+v[10]-v[2]-v[14])
            +(v[1]+v[2]-v[3])-(v[4]+v[8]-v[12]))
assert ingleton([min(3,S.bit_count()) for S in range(16)])==0
for direct in (ingleton(h),ingleton(z)):
    assert direct.lo<=j.hi and j.lo<=direct.hi
assert den.lo>0 and j.hi<0
score=j/den
assert score.lo>=F('-0.097387436923') and score.hi<=F('-0.097387436922')
assert score.hi<F('-0.09738')
# These positive enclosures complement the analytic comparisons in the paper.
thresh={3:bb,5:HH+P-a,9:a,6:a,10:HH+P-a,12:HH-d}
for S,t in thresh.items():
    if S!=3:assert (t-bb).lo>0
out={'status':'PASS','method':'exact Fractions; 42-term positive atanh series with rigorous rational tail',
     'source_atoms':len(law),'source_weights_P_Q_T':list(map(str,(P,Q,T))),
     'exact_finite_marginal_and_uniformity_checks':True,'all15_binary_rank_checks':True,
     'direct_Ingleton_definition_cross_checks':True,
     'b':bb.out(),'J':j.out(),'zN':den.out(),'score':score.out(),
     'all15_target':{''.join('ABCD'[i] for i in range(4) if S>>i&1):z[S].out() for S in range(1,16)},
     'six_thresholds':{''.join('ABCD'[i] for i in range(4) if S>>i&1):v.out() for S,v in thresh.items()},
     'scope':'Finite identities and numeric enclosure only; membership uses the manuscript proof.'}
(Path(__file__).resolve().parent/'VERIFICATION.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: exact 24-atom source, all15 ranks/marginals, partner uniformity, thresholds and score enclosure')
print('Score enclosure:',score.out())
