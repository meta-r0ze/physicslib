"""Mass flips are Higgs moves (no data).

Run from tools/pm_sector after rank6.py and place.py: python3 higgs_moves.py
A flip L -> R changes 3Y by +-3 and the weak pairing by +-1: the Higgs doublet's numbers. Moves
of the sector (28 roots) and gauge-neutral moves (20 roots, an A4) carry none of that, so with
those alone no flip is reachable. Higgs-type roots (colour 0, weak +-1, 3Y +-3) number 40, 10
per sign pair.
Result (2026-11-23): every one-step flip is a single Higgs-type root. Every two-step flip has 6
to 8 ordered paths with exactly one Higgs move (the other a sector or neutral move). With a rate
per path, the up/down offset is Delta/6 to Delta/8 (about 5 to 7); data c/s ~ 14, t/b ~ 41. The
multi-step amplitude is open.
"""
import pickle, json, numpy as np, collections
exec(open(__file__.replace('higgs_moves.py','base.py')).read())
d=json.load(open('sector_data.json'))
S5,S6=pickle.load(open('sectors.pkl','rb'))
L=sorted([s for s in S6 if len(s)==28],key=sorted); S=L[5]
cA,cB=map(np.array,d['colour_roots']); wk=np.array(d['weak_root']); y=np.array(d['charge_direction_scaled'])
q=lambda i:(ip(RA[i],cA),ip(RA[i],cB),ip(RA[i],wk),ip(RA[i],y))
neutral={i for i in range(240) if q(i)==(0,0,0,0)}
higgs={i for i in range(240) if q(i)[:2]==(0,0) and abs(q(i)[2])==1 and abs(q(i)[3])==3}
print('Higgs-type roots:',len(higgs),dict(collections.Counter(q(i)[2:] for i in higgs)))
allowed=set(S)|neutral|higgs
a,b,w,yy,CH,WL=pickle.load(open('placement.pkl','rb'))
rs={tuple(RA[i]):i for i in allowed}
cnt=collections.Counter()
for g in range(3):
    for ch in CH[g]:
        for sec,(Lk,Rk) in {'up':(('Q',0,1),('u',0)),'down':(('Q',0,-1),('d',0)),'lepton':(('L',-1),'e')}.items():
            h=RA[ch[Rk]]-RA[ch[Lk]]; n=ip(h,h)
            one=tuple(h) in rs and rs[tuple(h)] in higgs
            two=[(i,rs[tuple(h-RA[i])]) for i in allowed if tuple(h-RA[i]) in rs]
            twoH=sum(1 for i,j in two if (i in higgs)+(j in higgs)==1)
            cnt[(sec,n//2,'one Higgs move' if one else '-','two-step paths with one Higgs move',twoH)]+=1
for k,v in sorted(cnt.items()): print(v,k)
