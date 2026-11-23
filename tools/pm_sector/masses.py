"""Generation masses: register spectrum and flip (Yukawa) matrices on the derived sector (no data
inside the computation; lepton/quark ratios printed only for comparison).

Run from tools/pm_sector after place.py and export.py: python3 masses.py
1. Gauge-neutral roots (pairing 0 with the colour roots, the weak root and the charge direction)
   are 20 (an A4 system): key 0: 4 (the ring steps), key (0,1): 8, (1,0): 4, (1,1): 4.
   A stay/move register over the three generations with these counts has spectrum
   {-4, 8-4*sqrt3, 8+4*sqrt3}: mass ratios 1 : 13.9 : 194 (clock phases: 1 : 10.6 : 164).
   Leptons: 1 : 206.8 : 3477. The register spectrum is not the lepton spectrum.
2. Flip matrix F(g, g') = Delta^-k, k = root steps from L(g) to R(g') (step -> Delta rule).
   Masses are its singular values. Representative placement: up rank 1 (one heavy state),
   down rank 2 with ratio 44.1 (b/s ~ 44.7, scheme-dependent), leptons rank 2 with ratio 1.1.
   Over all allowed root choices: down ratio 44.1 in 1/3 of the choices; up rank 1 in 1/4;
   leptons never near tau/mu = 16.8. So the open choices must be fixed, and a single minimal
   path per entry is not enough (path counts and clock phases are not yet in the entries).
"""
import json, pickle, itertools, collections
import numpy as np
exec(open(__file__.replace("masses.py","base.py")).read())

d=json.load(open('sector_data.json'))
cA,cB=map(np.array,d['colour_roots']); wk=np.array(d['weak_root']); y=np.array(d['charge_direction_scaled']); t=np.array(d['time_vector'])
readout=lambda r:(ip(r,cA),ip(r,cB),ip(r,wk),ip(r,y))
KEYS=[(0,0),(0,1),(1,0),(1,1)]
cvec=cu-2*cv
rdc=lambda r:(lambda x:x if x<=21 else x-43)(int(np.asarray(r)@G@cvec)%43)
tab=collections.Counter()
for r in RA:
    neutral=readout(r)==(0,0,0,0)
    tab[(key(r),'neutral' if neutral else 'charged',ip(r,t),rdc(r))]+=1
print('gauge-neutral roots by (key, time pairing, clock reading):')
for k,v in sorted(tab.items()):
    if k[1]=='neutral': print('  ',v,k)
print('gauge-neutral totals by key:',dict(collections.Counter(k[0] for k,v in tab.items() for _ in range(v) if k[1]=='neutral')))
gens=[(0,1),(1,0),(1,1)]
def kadd(a,b): return ((a[0]+b[0])%2,(a[1]+b[1])%2)
M=np.zeros((3,3),complex)
for r in RA:
    if readout(r)!=(0,0,0,0): continue
    k=key(r); ph=np.exp(2j*np.pi*rdc(r)/43)
    for i,g in enumerate(gens):
        j=gens.index(kadd(g,k)) if kadd(g,k) in gens else None
        if k==(0,0): M[i,i]+=ph
        elif j is not None: M[j,i]+=ph
print('phase-weighted register (Hermitian:',np.allclose(M,M.conj().T),')')
print(np.round(M,4))
ev=np.linalg.eigvalsh(M); a=np.sort(np.abs(ev))
print('eigenvalues',np.round(ev,5),' mass ratios',np.round((a/a[0])**2,3))
print('leptons 1 : 206.768 : 3477.23')

d=json.load(open('sector_data.json'))
P_=d['placement']; gens=['(0,1)','(1,0)','(1,1)']
D=43.0
def steps(a,b): h=np.array(b)-np.array(a); return ip(h,h)//2
def F(sec,col=0):
    K=np.zeros((3,3),int)
    for i,g in enumerate(gens):
        for j,gp in enumerate(gens):
            if sec=='up': L=P_[g][f'Q_{col}_1']; R=P_[gp][f'u_{col}']
            if sec=='down': L=P_[g][f'Q_{col}_-1']; R=P_[gp][f'd_{col}']
            if sec=='lepton': L=P_[g]['L_-1']; R=P_[gp]['e']
            K[i,j]=steps(L,R)
    return K
for sec in ('up','down','lepton'):
    K=F(sec); W=D**(-K.astype(float))
    sv=np.sort(np.linalg.svd(W,compute_uv=False))
    print(sec,'step matrix k(L_g -> R_g\'):\n',K,'\n  singular-value mass ratios',np.round(sv/sv[0],2))
print('data (mass ratios within sector): up 1 : 588 : 79900 ; down 1 : 19.9 : 890 ; lepton 1 : 206.8 : 3477')

a,b,w,y,CH,WL=pickle.load(open('placement.pkl','rb'))
D=43.0
def red(ch):  # roots that enter the colour-0 and lepton flip matrices
    return tuple(tuple(RA[ch[k]]) for k in [('Q',0,1),('Q',0,-1),('u',0),('d',0),('L',-1),'e'])
U=[sorted(set(red(ch) for ch in CH[g])) for g in range(3)]
print('distinct relevant choices per generation:',[len(u) for u in U])
def steps(x,yv): h=np.array(yv)-np.array(x); return ip(h,h)//2
res=collections.defaultdict(collections.Counter)
for c0,c1,c2 in itertools.product(*U):
    C=[c0,c1,c2]
    # gens 1,2 must share Q roots (derived); skip combos that don't
    if C[1][0]!=C[2][0] or C[1][1]!=C[2][1]: continue
    for sec,(li,ri) in {'up':(0,2),'down':(1,3),'lepton':(4,5)}.items():
        K=np.array([[steps(C[i][li],C[j][ri]) for j in range(3)] for i in range(3)])
        W=D**(-K.astype(float)); sv=np.sort(np.linalg.svd(W,compute_uv=False))[::-1]
        rank=int((sv>1e-12*sv[0]).sum())
        ratio=round(sv[0]/sv[1],1) if rank>=2 else None
        res[sec][(rank,ratio)]+=1
for sec in res: print(sec,dict(sorted(res[sec].items(),key=lambda kv:-kv[1])))
