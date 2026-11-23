"""Flip matrices with path counts (no data in the computation; ratios printed for comparison).

Run from tools/pm_sector after place.py: python3 flip_paths.py
Entry F(g, g') = (number of ordered minimal root paths from L(g) to R(g')) * Delta^-k. Clock
phases are left out: a mass is a program at rest, the ring's zero mode, where a displacement
has phase 1.
Result (2026-11-23): every norm-4 transition has the same two-step path count, large enough to
cancel most of the 1/Delta. Over all allowed root choices the ratios are 2 to 6 in every sector
(data 17 to 588); the down ratio 44.1 of one path per entry is gone. So the amplitude is not a
plain sum over paths; one path per entry has no reading behind it either.
"""
import pickle, numpy as np, collections, itertools
exec(open('base.py').read())
a,b,w,y,CH,WL=pickle.load(open('placement.pkl','rb'))
D=43.0
rootset={tuple(r) for r in RA}
def paths(x,yv):
    h=np.array(yv)-np.array(x); n=ip(h,h)
    if n==2: return 1,1
    if n==4: return 2,sum(1 for s in RA if tuple(h-s) in rootset)
    if n==6: return 3,sum(1 for s in RA for t2 in RA if tuple(h-s-t2) in rootset)
    if n==0: return 0,1
    return n//2,None
print('two-step path count for every norm-4 vector is the same?',
      len({paths(RA[0],RA[0]+v)[1] for v in [RA[i]+RA[j] for i in range(0,240,17) for j in range(240) if ip(RA[i],RA[j])==0][:30]})==1)
def red(ch): return tuple(tuple(RA[ch[k]]) for k in [('Q',0,1),('Q',0,-1),('u',0),('d',0),('L',-1),'e'])
U=[sorted(set(red(ch) for ch in CH[g])) for g in range(3)]
res=collections.defaultdict(collections.Counter); cache={}
def entry(x,yv):
    k=(x,yv)
    if k not in cache:
        st,m=paths(x,yv); cache[k]=(st,m)
    return cache[k]
for c0,c1,c2 in itertools.product(*U):
    C=[c0,c1,c2]
    if C[1][0]!=C[2][0] or C[1][1]!=C[2][1]: continue
    for sec,(li,ri) in {'up':(0,2),'down':(1,3),'lepton':(4,5)}.items():
        W=np.zeros((3,3))
        for i in range(3):
            for j in range(3):
                st,m=entry(C[i][li],C[j][ri]); W[i,j]=m*D**(-st)
        sv=np.sort(np.linalg.svd(W,compute_uv=False))[::-1]
        rank=int((sv>1e-12*sv[0]).sum())
        res[sec][(rank,round(sv[0]/sv[1],1) if rank>=2 else None, round(sv[1]/sv[2],1) if rank==3 else None)]+=1
for sec in res: print(sec,dict(sorted(res[sec].items(),key=lambda kv:-kv[1])))
print('data: up t/c 136, c/u 588 ; down b/s 44.7, s/d 19.9 ; lepton tau/mu 16.8, mu/e 206.8')
