#!/usr/bin/env python3
"""Leg-count tests (PMAction REVIEW k/K; PMFlavor REVIEW node edges): leave/enter amplitude pairs against
|V_cb|/|V_ub|, and the same asymmetry on the wire light insertions against the charge-weight test."""
import numpy as np, itertools
from scipy.optimize import brentq
from scipy.optimize import brentq
a=1/137.035999
d=dict(Vcb=0.0410,Vcb_incl=0.0422,Vcb_excl=0.0398,Vub=0.00382,Vub_incl=0.00413,Vub_excl=0.00370)
amps={'a':a,'a/2':a/2,'a/3':a/3,'sqrt(a)':np.sqrt(a),'sqrt(a)/2':np.sqrt(a)/2,'sqrt(a/2)':np.sqrt(a/2),'2a':2*a}
print("ratio data Vcb/Vub = %.2f"%(d['Vcb']/d['Vub']))
rows=[]
for (nl,al),(ne,ae) in itertools.product(amps.items(),repeat=2):
    rows.append((abs(np.log((al/ae)/(d['Vcb']/d['Vub']))),nl,ne,al,ae,al/ae))
rows.sort()
print("leave/enter amplitude pairs closest to the ratio (a common factor g left free):")
for r in rows[:6]:
    g=np.sqrt(d['Vcb']*d['Vub']/(r[3]*r[4]))
    print("  leave %-9s enter %-9s ratio %.2f  common factor g=%.3f -> Vcb %.4f Vub %.5f"%(r[1],r[2],r[5],g,g*r[3],g*r[4]))
print("no free factor: Vcb=sqrt(a)/2=%.4f  Vub=a/2=%.5f"%(np.sqrt(a)/2,a/2))

a=1/137.035999
P=np.zeros((3,3)); P[1,0]=P[2,1]=P[0,2]=1
def M(d,s,k1,k2):
    X=d*np.eye(3,dtype=complex)+P
    return np.diag([s,k1,k2])@X@np.diag([s,1,1])
def sv(m): return np.sort(np.linalg.svd(m,compute_uv=False))
def weight(t,k1,k2):
    ss=np.logspace(-3,3,6000); f=lambda s: sv(M(-1,s,k1,k2))[1]/sv(M(-1,s,k1,k2))[2]-t
    v=[f(s) for s in ss]; r=[brentq(f,ss[i],ss[i+1]) for i in range(len(ss)-1) if v[i]*v[i+1]<0]
    return r[0] if r else np.nan
for name,(k1,k2) in {'sym a/2':(a/2,a/2),'enter a/2, leave sqrt(a)/2':(a/2,np.sqrt(a)/2),'leave, enter swapped':(np.sqrt(a)/2,a/2),'enter a, leave sqrt(a)':(a,np.sqrt(a))}.items():
    s0=sv(M(-1,1,k1,k2))
    se,sd,su=[weight(t,k1,k2) for t in (0.0595,0.0199,0.00372)]
    ad=np.log(sd/se)/(4/3); au=np.log(su/se)/(10/3)
    print(f"{name:30s} bare m2/m3 {s0[1]/s0[2]:.4f} m1 {s0[0]:.1e} | s_e {se:.3f} s_d {sd:.3f} s_u {su:.3f} | charge a from d {ad:.3f}, from u {au:.3f} (gap {abs(ad-au)/((ad+au)/2)*100:.0f}%)")
