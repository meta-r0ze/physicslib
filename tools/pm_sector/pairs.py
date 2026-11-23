"""See place.py for the readings and results; prints step counts of the mass-pair transitions."""
import pickle, collections, numpy as np
exec(open('base.py').read())
a,b,w,y,CH,WL=pickle.load(open('placement.pkl','rb'))
cvec=cu-2*cv
def rdc(v): x=int(np.asarray(v)@G@cvec)%43; return x if x<=21 else x-43
t=None
fwd=[i for i in range(240) if all(P[i,j]==0 for j in Dint) and rdc(RA[i])==1]
t=next(RA[i]+RA[j] for i in fwd for j in fwd if i!=j and P[i,j]==0)
KEYS=[(0,1),(1,0),(1,1)]
def kv(v): return ((ip(v,A_)+ip(v,C_))%2,(ip(v,A_)+ip(v,BE_))%2)
for sigma in (1,-1):
  print('== weak sign convention sigma =',sigma)
  for g in range(3):
    stats=collections.defaultdict(set)
    for ch in CH[g]:
        for sec,R_,m in [('up','u',sigma),('down','d',-sigma),('lepton','e',-sigma)]:
            hs=[]
            for col in (range(3) if sec!='lepton' else [None]):
                rR=RA[ch[(R_,col)]] if col is not None else RA[ch['e']]
                rL=RA[ch[('Q',col,m)]] if col is not None else RA[ch[('L',m)]]
                hs.append(rR-rL)
            inv=tuple(sorted({(ip(h,h),rdc(h),int(h@G@t),kv(h)) for h in hs}))
            stats[sec].add(inv)
    for sec in ('up','down','lepton'):
        print('  gen',KEYS[g],sec,'(norm, clock reading, time pairing, key) over all choices:',sorted(stats[sec])[:4],'...' if len(stats[sec])>4 else '', len(stats[sec]),'distinct')
print('== joint (up, down, lepton) step counts per root choice, sigma=1')
for g in range(3):
    jc=collections.Counter()
    for ch in CH[g]:
        row=[]
        for sec,R_,m in [('up','u',1),('down','d',-1),('lepton','e',-1)]:
            col=0 if sec!='lepton' else None
            rR=RA[ch[(R_,0)]] if col is not None else RA[ch['e']]
            rL=RA[ch[('Q',0,m)]] if col is not None else RA[ch[('L',m)]]
            h=rR-rL; row.append(ip(h,h)//2)
        jc[tuple(row)]+=1
    print('  gen',KEYS[g],dict(jc))
