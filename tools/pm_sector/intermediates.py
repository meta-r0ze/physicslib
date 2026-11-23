"""Step -> Delta rule: intermediates of multi-step mass transitions cannot persist (no data).

Run from tools/pm_sector after place.py: python3 intermediates.py
For every two-step charge-correct mass transition h = r_right - r_left on the derived sector,
list its decompositions h = s1 + s2 into roots and test the intermediate r_left + s1.
Result (2026-11-23): the intermediate is never a channel, except for down pairs in generations
(1,0) and (1,1) in half the root choices, where it is u_R of the same colour and generation
(Q_down -> u_R -> d_R). u_R has charge +2/3 against the down quark's -1/3, so that stage breaks
charge conservation.
Rule, from library readings: mass is the rate of the left <-> right record flip; at least Toll a
root move fires once per 43-tick period (ProgramWitness.witness_total, RingRates.one_site_exact),
probability 1/Delta per tick; an intermediate that is not a channel is not a record (Map) and one
with another charge is not conserved (Conservation), so it cannot persist across a tick and all
k steps fire in one tick: flip rate ~ Delta^-k. With pairs.py: up/down offset = one power of
Delta in generations (1,0) and (1,1).
"""
import pickle, collections, numpy as np
exec(open('base.py').read())
a,b,w,y,CH,WL=pickle.load(open('placement.pkl','rb'))
KEYS=[(0,1),(1,0),(1,1)]
rootset={tuple(r) for r in RA}
stats=collections.Counter()
for g in range(3):
    for ch in CH[g]:
        chanset={tuple(RA[v]) for v in ch.values()}
        for sec,R_,m in [('up','u',1),('down','d',-1),('lepton','e',-1)]:
            for col in (range(3) if sec!='lepton' else [None]):
                rR=RA[ch[(R_,col)]] if col is not None else RA[ch['e']]
                rL=RA[ch[('Q',col,m)]] if col is not None else RA[ch[('L',m)]]
                h=rR-rL; n=ip(h,h)//2
                if n!=2: continue
                mids=[tuple(rL+s) for s in RA if ip(s,s)==2 and tuple(h-s) in rootset]
                inroot=[x for x in mids if x in rootset]
                inchan=[x for x in inroot if x in chanset]
                stats[(KEYS[g],sec,'2-step: decompositions',len(mids),'intermediate is a root',len(inroot),'is a channel of this generation',len(inchan))]+=1
for k,v in sorted(stats.items()): print(v,k)
print('---- which channel is the intermediate')
who=collections.Counter()
for g in (1,2):
    for ci,ch in enumerate(CH[g]):
        inv={tuple(RA[v]):k for k,v in ch.items()}
        for col in range(3):
            rR=RA[ch[('d',col)]]; rL=RA[ch[('Q',col,-1)]]; h=rR-rL
            for s in RA:
                if ip(s,s)==2 and tuple(h-s) in rootset and tuple(rL+s) in inv:
                    k=inv[tuple(rL+s)]
                    step1=s; step2=h-s
                    tag=lambda v:'weak root' if (tuple(v)==tuple(RA[w]) or tuple(v)==tuple(-RA[w])) else ('pairs with t:%d'%int(v@G@(RA[0]*0+0)) if False else 'other')
                    who[(KEYS[g],'colour',col,'d_R from Q_down via',k if not isinstance(k,tuple) else k[:2]+((k[2],) if len(k)>2 else ()),'first step',tag(step1))]+=1
for k,v in sorted(who.items()): print(v,k)
