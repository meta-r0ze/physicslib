#!/usr/bin/env python3
"""Order-alpha correction to the muon width at fixed neutrino-pair invariant, derived from the
diagrams (external, numerical certificate; EP REVIEW, radiative factor).

The vertex is the substrate's conserved wall vertex in its continuum form (PMAction.SpinorVertex:
Ward identity exact, Z1 = Z2), photons are emitted into continuum modes (PolarMeasure, NullBoost).
Muon (mass 1) -> electron (mass me) + V(q), V-A current, pair tensor q_a q_b - q^2 g_ab
(PairSphere). Explicit Dirac matrices; regulators: Pauli-Villars photon (UV), photon mass lam (IR),
electron mass me (collinear).
* virtual: one-loop vertex by Feynman parameters, plus on-shell Z2 of both legs;
* real: massive-photon emission over the three-body phase space at fixed q^2 = z;
Checks: the sum is independent of the PV mass (UV) and of lam as lam -> 0 (IR), and as me -> 0 it
tends to the published inclusive kernel F1 (Kuehn-Mirkes Eq. (52), tools/muon_radiative_certificate.py),
which integrates to pi^2 - 25/4. That kernel is a cross-check, not an input.
Output units: Delta Gamma(z)/Gamma0(z) in alpha/(4 pi); the kernel value is -2 F1(z)/F0(z).
Results (me = 3e-4, lam = me*1e-4):
  z = 0.1: -7.76176 (kernel -7.76131); 0.3: -7.37098 (-7.37086); 0.5: -6.88717 (-6.88718);
  0.7: -5.69915 (-5.69929); 0.9: -1.54393 (-1.54503); residuals shrink with me.
Usage: muon_radiative_derivation.py z me [me ...]   (about 2 minutes per point)
"""
import numpy as np
I2=np.eye(2); Z2=np.zeros((2,2))
sx=np.array([[0,1],[1,0]],complex); sy=np.array([[0,-1j],[1j,0]]); sz=np.array([[1,0],[0,-1]],complex)
g0=np.block([[I2,Z2],[Z2,-I2]]).astype(complex)
gs=[np.block([[Z2,s],[-s,Z2]]) for s in (sx,sy,sz)]
G=[g0]+gs
g5=1j*G[0]@G[1]@G[2]@G[3]
eta=np.diag([1.,-1,-1,-1])
I4=np.eye(4,dtype=complex)
def sl(p): return sum(eta[m,m]*p[m]*G[m] for m in range(4))
def dot(a,b): return a[0]*b[0]-a[1]*b[1]-a[2]*b[2]-a[3]*b[3]
Gam=[G[a]@(I4-g5) for a in range(4)]           # V-A vertex gamma^a (1-g5)
def bar(M): return g0@M.conj().T@g0
GamBar=[bar(x) for x in Gam]
def Ttensor(q):
    z=dot(q,q); ql=eta@q
    return np.outer(ql,ql)-z*eta     # lower indices T_ab = q_a q_b - z g_ab
def contract(V,Vb,pp,me,p,m,q):
    """sum_ab Tr[(pp/+me) V^a (p/+m) Vb^b] T_ab ; V,Vb lists over upper index a"""
    T=Ttensor(q); A=sl(pp)+me*I4; B=sl(p)+m*I4
    tot=0
    for a in range(4):
        for b in range(4):
            if T[a,b]!=0: tot+=np.trace(A@V[a]@B@Vb[b])*T[a,b]
    return tot
def kin2(z,m=1.0,me=0.0):
    """two-body mu -> e + V(z) in rest frame"""
    Ee=(m*m+me*me-z)/(2*m); pe=np.sqrt(max(Ee*Ee-me*me,0))
    p=np.array([m,0,0,0.]); pp=np.array([Ee,0,0,pe]); q=p-pp
    return p,pp,q,pe
def F0(z): return 2*(1-z)**2*(1+2*z)
from scipy.integrate import quad

def gsand(X):  # gamma^rho X gamma_rho
    return sum(eta[r,r]*G[r]@X@G[r] for r in range(4))

def vertex_ratio(z,me,lam,LamPV,m=1.0):
    """2 Re[M0* Lambda] / |M0|^2 in units of alpha/(4pi) ... returns coefficient c with ratio=(alpha/4pi)*c"""
    p,pp,q,pe=kin2(z,m,me)
    M0=contract(Gam,GamBar,pp,me,p,m,q).real
    U=[sl(pp),sl(p),me*I4]; V=[sl(p),sl(pp),m*I4]
    S=np.zeros((3,3))
    for i in range(3):
        for j in range(3):
            Vmat=[gsand(U[i]@Gam[a]@V[j]) for a in range(4)]
            S[i,j]=contract(Vmat,GamBar,pp,me,p,m,q).real
    ppd=dot(p,pp)
    def f(x,y):
        w=1-x-y
        P2=x*x*me*me+y*y*m*m+2*x*y*ppd
        D=P2+w*lam*lam; DPV=P2+w*LamPV**2
        cu=[(1-x),-y,1.0]; cv=[(1-y),-x,1.0]
        n0=sum(cu[i]*cv[j]*S[i,j] for i in range(3) for j in range(3))
        return -n0/D + 2*M0*np.log(DPV/D)
    # polar: x=r u, y=r(1-u); jac r ; log variables
    def inner(r):
        g=lambda u: f(r*u,r*(1-u))*r
        # collinear peak near u=1 (y->0): map 1-u = exp(t)
        a=quad(lambda t: g(1-np.exp(t))*np.exp(t), np.log(1e-16), np.log(0.5), limit=400, epsabs=0, epsrel=1e-11)[0]
        b=quad(g, 0, 0.5, limit=400, epsabs=0, epsrel=1e-11)[0]
        return a+b
    tot=quad(lambda s: inner(np.exp(s))*np.exp(s), np.log(1e-16), 0, limit=400, epsabs=0, epsrel=1e-10)[0]
    return 2*tot/M0   # 2 Re

def dZ(M,lam,LamPV):
    """delta Z2 in units of alpha/(4pi)"""
    L=lambda x: np.log((x*x*M*M+(1-x)*LamPV**2)/(x*x*M*M+(1-x)*lam*lam))
    A=quad(lambda x: -2*(1-x)*L(x),0,1,limit=400,points=[1e-8,1e-4],epsrel=1e-12)[0]
    def Lp(x):
        D=x*x*M*M+(1-x)*lam*lam; DP=x*x*M*M+(1-x)*LamPV**2
        return x*(1-x)/D - x*(1-x)/DP
    Ap=quad(lambda x: -2*(1-x)*Lp(x),0,1,limit=400,points=[lam/M*1e-3,lam/M,lam/M*1e3] if M>0 else None,epsrel=1e-12)[0]
    Bp=quad(lambda x: 4*Lp(x),0,1,limit=400,points=[lam/M*1e-3,lam/M,lam/M*1e3],epsrel=1e-12)[0]
    return A+2*M*M*(Ap+Bp)

from scipy.integrate import quad
from scipy.optimize import brentq

def M2real(p,pp,k,me,m,q,lam):
    D1=2*dot(pp,k)+lam*lam; D2=lam*lam-2*dot(p,k)
    A=sl(pp)+sl(k)+me*I4; B=sl(p)-sl(k)+m*I4
    tot=0
    for r in range(4):
        O=[G[r]@A@Gam[a]/D1 + Gam[a]@B@G[r]/D2 for a in range(4)]
        Ob=[bar(x) for x in O]
        tot+=-eta[r,r]*contract(O,Ob,pp,me,p,m,q).real
    return tot

def real_ratio(z,me,lam,m=1.0,rtol=1e-9):
    """[int |M_R|^2 dPhi3]/[|M0|^2 Phi2] in units alpha/(4pi) (e^2=4pi alpha -> factor 16 pi^2)"""
    p0,pp0,q0,pe0=kin2(z,m,me)
    M0=contract(Gam,GamBar,pp0,me,p0,m,q0).real; Phi2=pe0/(4*np.pi*m)
    p=np.array([m,0,0,0.])
    Egmax=(m*m+lam*lam-(me+np.sqrt(z))**2)/(2*m)
    def cosof(Ee,Eg):
        s1=2*m*Ee-(m*m+me*me+lam*lam-2*m*Eg-z)
        pe=np.sqrt(max(Ee*Ee-me*me,0)); kk=np.sqrt(max(Eg*Eg-lam*lam,0))
        return (Ee*Eg-s1/2)/(pe*kk) if pe*kk>0 else np.inf
    def point(Ee,Eg):
        c=cosof(Ee,Eg); c=min(1,max(-1,c))
        pe=np.sqrt(Ee*Ee-me*me); kk=np.sqrt(Eg*Eg-lam*lam)
        pp=np.array([Ee,0,0,pe]); k=np.array([Eg,kk*np.sqrt(1-c*c),0,kk*c])
        q=p-pp-k
        return M2real(p,pp,k,me,m,q,lam)
    def Ee_bounds(Eg):
        # cos(E_e) is decreasing; endpoints where cos = +1 (lo) and cos = -1 (hi)
        kk=np.sqrt(max(Eg*Eg-lam*lam,0))
        C=m*m+me*me+lam*lam-2*m*Eg-z
        Ec=C/(2*(m-Eg))                    # cos = 0
        if Ec<=me: return None
        pc=np.sqrt(Ec*Ec-me*me)
        w=max(4*pc*kk/(m-Eg),1e-300)
        def solve(target,direction):
            a=Ec; step=w
            for _ in range(200):
                b=a+direction*step
                if b<=me: b=me*(1+1e-15)
                if (cosof(b,Eg)-target)*(cosof(a,Eg)-target)<=0:
                    return brentq(lambda E: cosof(E,Eg)-target, min(a,b), max(a,b), xtol=1e-300, rtol=1e-15)
                if b<=me*(1+1e-15): return b
                a=b; step*=2
            return a
        lo=solve(1.0,-1); hi=solve(-1.0,+1)
        if not hi>lo: return None
        return lo,hi,None
    def inner(Eg):
        b=Ee_bounds(Eg)
        if b is None: return 0.0
        lo,hi,_=b
        # collinear end is where cos=+1; map log distance to both ends
        mid=(lo+hi)/2
        f=lambda E: point(E,Eg)
        a1=quad(lambda t: f(lo+np.exp(t))*np.exp(t), np.log((hi-lo)*1e-14), np.log(mid-lo), limit=300, epsrel=rtol)[0]
        a2=quad(lambda t: f(hi-np.exp(t))*np.exp(t), np.log((hi-lo)*1e-14), np.log(hi-mid), limit=300, epsrel=rtol)[0]
        return a1+a2
    # soft: integrate in u = ln|k|
    def outer(u):
        kk=np.exp(u); Eg=np.sqrt(kk*kk+lam*lam)
        return inner(Eg)*kk/Eg*kk   # dEg = k dk/Eg, dk = k du
    kmax=np.sqrt(Egmax**2-lam*lam)
    tot=quad(outer, np.log(kmax*1e-12), np.log(kmax), limit=300, epsrel=rtol, points=[np.log(lam)] if lam<kmax else None)[0]
    X=tot/(32*np.pi**3)       # int |M|^2 dEe dEg /(32 pi^3), e^2 stripped
    return 16*np.pi**2*X/(M0*Phi2)   # e^2 = 4 pi alpha; ratio in units alpha/(4 pi)

from scipy.special import spence
def F1(z):
    return (F0(z)*(np.pi**2+2*(spence(1-z)-spence(z)))+4*z*(1-z-2*z*z)*np.log(z)
            +2*(1-z)**2*(5+4*z)*np.log1p(-z)-(1-z)*(5+9*z-6*z*z))

if __name__ == "__main__":
    import sys, warnings
    warnings.simplefilter("ignore")
    z = float(sys.argv[1]) if len(sys.argv) > 1 else 0.5
    mes = [float(x) for x in sys.argv[2:]] or [1e-3]
    print(f"z = {z}: kernel (alpha/4pi) {-2*F1(z)/F0(z):.6f}")
    for me in mes:
        lam = me * 1e-4
        v = vertex_ratio(z, me, lam, 1e4) + dZ(1.0, lam, 1e4) + dZ(me, lam, 1e4)
        r = real_ratio(z, me, lam, rtol=1e-8)
        print(f"  me = {me}: virtual {v:.6f}, real {r:.6f}, sum {v + r:.6f}")
