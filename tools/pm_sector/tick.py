exec(open('sector.py').read().split("if __name__")[0])
import pickle
S5,S6=pickle.load(open('sectors.pkl','rb'))
rdi=lambda i:(lambda x:x if x<=21 else x-43)(rd(R[i]))
axis=[i for i in Dst if rdi(i) in (1,-1)]
print('clock-axis roots',len(axis),' slice roots',len([i for i in Dst if rdi(i)==0]))
# orthogonality pattern of slice roots to clock-axis roots
for i in [i for i in Dst if rdi(i)==0][:3]: print(' slice root pairings with axis roots',sorted(P[i,j] for j in axis))
L=sorted([s for s in S6 if len(s)==28],key=sorted)
# extend test: y also orthogonal to the clock-axis roots
def test_tick(S):
    import types
    g=dict(globals())
    return None
for k,S in enumerate(L):
    ext=sorted({min(a,int(neg[a])) for a in S if a not in Dint})
    perp=[all(P[a,j]==0 for j in axis) for a in ext]
    print(k,'extra roots readings',[rdi(a) for a in ext],'orthogonal to every clock-axis root:',perp)
fwd=[i for i in axis if rdi(i)==1]
ts={tuple(RA[i]+RA[j]) for i in fwd for j in fwd if i!=j and P[i,j]==0}
print('time vectors from orthogonal forward pairs:',len(ts),[ (ip(t,t)) for t in ts])
t=np.array(list(ts)[0])
print('forward axis roots pair with t:',sorted(int(RA[i]@G@t) for i in fwd))
for k,S in enumerate(L):
    ext=sorted({min(a,int(neg[a])) for a in S if a not in Dint})
    print(k,'readings',[rdi(a) for a in ext],'pairing with t',[int(RA[a]@G@t) for a in ext])
exec(open('sector.py').read().split("if __name__")[0])
for k in (2,5,8):
    S=L[k]
    print(k,'with y orthogonal to t:',dict(test(S,True,True,extra_orth=[t])),flush=True)
