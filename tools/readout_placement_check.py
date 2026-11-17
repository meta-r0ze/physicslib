"""Where can a per-protocol knob enter the derived wire? (EP REVIEW, Toll.)

For each placement, the knob value that reproduces each protocol m2/m3 on the resonance (k = alpha/2),
with the lightest-to-heaviest ratio it implies. Data m2/m3: nu 0.17 (normal ordering, m1 = 0), e 0.0595,
d 0.0199, u 0.00372; data m1/m3: e 2.9e-4, d 1.1e-3, u 1.3e-5."""
import numpy as np
from scipy.optimize import brentq
a=1/137.035999; k=a/2; d=-1
def X(kO=(1,1,1)):
    M=d*np.eye(3,dtype=complex); M[1,0]+=kO[0]; M[2,1]+=kO[1]; M[0,2]+=kO[2]; return M
def m23(M):
    sv=np.sort(np.linalg.svd(M,compute_uv=False)); return sv[1]/sv[2], sv[0]/sv[2]
P={
 'both walls (current)': lambda s: np.diag([s,k,k])@X()@np.diag([s,1,1]),
 'reference wall only':  lambda s: np.diag([s,k,k])@X()@np.eye(3),
 'other wall only':      lambda s: np.diag([1,k,k])@X()@np.diag([s,1,1]),
 'node amplitude k->k*s':lambda s: np.diag([1,k*s,k*s])@X(),
 'other-wall cycle leg (s,1,1)': lambda s: np.diag([1,k,k])@X((s,1,1)),
 'other-wall cycle leg (1,s,1)': lambda s: np.diag([1,k,k])@X((1,s,1)),
 'other-wall cycle leg (1,1,s)': lambda s: np.diag([1,k,k])@X((1,1,s)),
 'detuning delta*s':     lambda s: np.diag([1,k,k])@((d*s)*np.eye(3)+X()-d*np.eye(3)),
}
T={'nu':0.17,'e':0.0595,'d':0.0199,'u':0.00372}
for name,f in P.items():
    ss=np.logspace(-4,4,8001); out={}
    for p,t in T.items():
        v=[m23(f(s))[0]-t for s in ss]
        r=[brentq(lambda s:m23(f(s))[0]-t,ss[i],ss[i+1]) for i in range(len(ss)-1) if v[i]*v[i+1]<0]
        out[p]=r
    print(name); 
    for p,r in out.items(): print('   ',p,[f'{x:.4g}' for x in r[:4]], ['m1/m3=%.1e'%m23(f(x))[1] for x in r[:2]])
