#!/usr/bin/env python3
"""Cheap tests of CKM sources on the derived wire (PMElementaryParticles REVIEW, Mixing).
Blocks: (1) one-parameter deformations fitted to |V_us|; (2) heavy-label weight placement, refit;
(3) flip phase x light-class asymmetry fitted to |V_us|, |V_cb|; (4) k/K scan with weights refit."""

print('=== block mix')
import numpy as np
from scipy.optimize import brentq
a=1/137.035999; k=a/2
P=np.zeros((3,3)); P[1,0]=P[2,1]=P[0,2]=1
su,sd=np.sqrt(1.3066),np.sqrt(0.0670); eu,ed=0.00236,0.1396
data=(0.2250,0.0410,0.00369)
def M(d,s,kR=(1,k,k),kO=(1,1,1)):
    X=d*np.eye(3,dtype=complex); X[1,0]+=kO[0]; X[2,1]+=kO[1]; X[0,2]+=kO[2]
    return np.diag([s*kR[0],kR[1],kR[2]])@X@np.diag([s,1,1])
def U(m,side='L'):
    h=m@m.conj().T if side=='L' else m.conj().T@m
    return np.linalg.eigh(h)[1]
def V(Mu,Md,side='L'):
    v=np.abs(U(Mu,side).conj().T@U(Md,side)); return v[0,1],v[1,2],v[0,2]
def ratios(m):
    s=np.sort(np.linalg.svd(m,compute_uv=False)); return s[0]/s[1],s[1]/s[2]
base_u=lambda **kw: M(-(1-eu),su,**kw); base_d=lambda **kw: M(-(1-ed),sd,**kw)
print("baseline L:",np.round(V(base_u(),base_d()),4)," R:",np.round(V(base_u(),base_d(),'R'),4))
def scan(name,fu,fd,ps):
    vals=[]
    for p in ps:
        Mu,Md=fu(p),fd(p); vals.append((p,)+V(Mu,Md)+ratios(Mu)+ratios(Md))
    vals=np.array(vals)
    # closest to Vus
    i=np.argmin(abs(vals[:,1]-data[0]))
    p=vals[i]
    print(f"{name}: best p={p[0]:.4g}  Vus {p[1]:.4f} Vcb {p[2]:.4f} Vub {p[3]:.4f} | up m1/m2 {p[4]:.4f} m2/m3 {p[5]:.4f} | down {p[6]:.4f} {p[7]:.4f}")
ps=np.linspace(0,np.pi,2001)
# M3: relative phase of down's flip root
scan("M3 relative flip phase", lambda p: M(-(1-eu),su), lambda p: M(-(1-ed)*np.exp(1j*p),sd), ps)
# M4: light-class asymmetry k_s != k_c, swapped between up and down (DoubletReflection)
rs=np.logspace(-2,2,2001)
scan("M4 k_s/k_c asymmetry", lambda r: M(-(1-eu),su,kR=(1,k*np.sqrt(r),k/np.sqrt(r))), lambda r: M(-(1-ed),sd,kR=(1,k/np.sqrt(r),k*np.sqrt(r))), rs)
# M8: cycle phase on the other wall, opposite for up and down
scan("M8 other-wall cycle phase ±φ", lambda p: M(-(1-eu),su,kO=(1,1,np.exp(1j*p))), lambda p: M(-(1-ed),sd,kO=(1,1,np.exp(-1j*p))), ps)
scan("M8b cycle phase on down only", lambda p: M(-(1-eu),su), lambda p: M(-(1-ed),sd,kO=(1,1,np.exp(1j*p))), ps)
# M9: other-wall light asymmetry k_O
scan("M9 other wall kO=(1,r,1/r) swapped", lambda r: M(-(1-eu),su,kO=(1,r,1/r)), lambda r: M(-(1-ed),sd,kO=(1,1/r,r)), rs)

print('=== block mix2')
import numpy as np
from scipy.optimize import brentq, minimize
a=1/137.035999; k=a/2
data=(0.2250,0.0410,0.00369)
tgt={'u':(0.0017,0.0037),'d':(0.050,0.0199),'e':(0.00484,0.0595)}
def M(d,s,place,kR=(1,k,k),kO=(1,1,1)):
    X=d*np.eye(3,dtype=complex); X[1,0]+=kO[0]; X[2,1]+=kO[1]; X[0,2]+=kO[2]
    L=np.diag([kR[0],kR[1],kR[2]]).astype(complex); R=np.eye(3,dtype=complex)
    if place in('L','LR'): L[0,0]*=s
    if place in('R','LR'): R[0,0]*=s
    if place=='L2': L[0,0]*=s*s
    return L@X@R
def rat(m):
    s=np.sort(np.linalg.svd(m,compute_uv=False)); return np.array([s[0]/s[1],s[1]/s[2]])
def fit(p,place,**kw):
    f=lambda x: np.sum(np.log(rat(M(-(1-x[1]),np.exp(x[0]),place,**kw))/np.array(tgt[p]))**2)
    best=None
    for x0 in [(-2,0.01),(0,0.01),(1,0.01),(-1,0.1),(0.5,0.001)]:
        r=minimize(f,x0,method='Nelder-Mead',options={'xatol':1e-10,'fatol':1e-14,'maxiter':4000})
        if best is None or r.fun<best.fun: best=r
    return best
def U(m): return np.linalg.eigh(m@m.conj().T)[1]
for place in ['LR','L','R','L2']:
    fu,fd=fit('u',place),fit('d',place)
    Mu=M(-(1-fu.x[1]),np.exp(fu.x[0]),place); Md=M(-(1-fd.x[1]),np.exp(fd.x[0]),place)
    v=np.abs(U(Mu).conj().T@U(Md))
    print(place,"fit res %.1e %.1e"%(fu.fun,fd.fun),"s_u %.3f s_d %.3f eps %.4f %.4f"%(np.exp(fu.x[0]),np.exp(fd.x[0]),fu.x[1],fd.x[1]),
          "Vus %.4f Vcb %.4f Vub %.4f"%(v[0,1],v[1,2],v[0,2]))

print('=== block mix3')
import numpy as np
a=1/137.035999; k=a/2
su,sd=np.sqrt(1.3066),np.sqrt(0.0670); eu,ed=0.00236,0.1396
def M(d,s,kR):
    X=d*np.eye(3,dtype=complex); X[1,0]+=1; X[2,1]+=1; X[0,2]+=1
    return np.diag([s*kR[0],kR[1],kR[2]])@X@np.diag([s,1,1])
def U(m): return np.linalg.eigh(m@m.conj().T)[1]
def rat(m):
    s=np.sort(np.linalg.svd(m,compute_uv=False)); return s[0]/s[1],s[1]/s[2]
best=[]
for lr in np.linspace(-3,3,241):
  r=np.exp(lr)
  for th in np.linspace(0,np.pi,181):
    Mu=M(-(1-eu),su,(1,k*np.sqrt(r),k/np.sqrt(r))); Md=M(-(1-ed)*np.exp(1j*th),sd,(1,k/np.sqrt(r),k*np.sqrt(r)))
    v=np.abs(U(Mu).conj().T@U(Md)); cost=np.log(v[0,1]/0.225)**2+np.log(v[1,2]/0.041)**2
    best.append((cost,r,th,v[0,1],v[1,2],v[0,2])+rat(Mu)+rat(Md))
best.sort()
for b in best[:5]: print("cost %.3f r %.3g th %.3f Vus %.4f Vcb %.4f Vub %.4f | up %.4f %.4f down %.4f %.4f"%b)
# what is max Vcb reachable at all
print("max Vcb over grid: %.4f"%max(b[4] for b in best))

print('=== block mix4')
import numpy as np
from scipy.optimize import minimize
a=1/137.035999
tgt={'u':(0.0017,0.0037),'d':(0.050,0.0199)}
def M(d,s,k):
    X=d*np.eye(3,dtype=complex); X[1,0]+=1; X[2,1]+=1; X[0,2]+=1
    return np.diag([s,k,k])@X@np.diag([s,1,1])
def rat(m):
    s=np.sort(np.linalg.svd(m,compute_uv=False)); return np.array([s[0]/s[1],s[1]/s[2]])
def fit(p,k):
    f=lambda x: np.sum(np.log(rat(M(-(1-x[1]),np.exp(x[0]),k))/np.array(tgt[p]))**2)
    return min((minimize(f,x0,method='Nelder-Mead',options={'xatol':1e-10,'fatol':1e-14,'maxiter':4000}) for x0 in [(-2,0.01),(0,0.01),(1,0.01),(-1,0.1),(2,0.001)]),key=lambda r:r.fun)
def U(m): return np.linalg.eigh(m@m.conj().T)[1]
for mult in [0.5,1,2,5,10,20]:
    k=mult*a/2; fu,fd=fit('u',k),fit('d',k)
    Mu=M(-(1-fu.x[1]),np.exp(fu.x[0]),k); Md=M(-(1-fd.x[1]),np.exp(fd.x[0]),k)
    v=np.abs(U(Mu).conj().T@U(Md))
    print("k=%.4f res %.0e %.0e Vus %.4f Vcb %.4f Vub %.4f"%(k,fu.fun,fd.fun,v[0,1],v[1,2],v[0,2]))
