#!/usr/bin/env python3
"""Certificate for the confined carrier's rms radius on the 3^3 cube (PMAction REVIEW A.1).

Exact arithmetic (sympy, Gaussian rationals) plus interval arithmetic (mpmath.iv); no floating
point enters the result.
1. H = I (x) H0 - sum_j N_j (ConfinedCarrier, plain truncation) is built with entries in Q(i).
2. K_k = H^k s0, s0 = one spinor component on the centre site, k = 0..28. Their exact linear
   relation gives the monic minimal polynomial P (degree 28) of H on this cyclic subspace; the
   degree-14 integer polynomial f below divides it, and f has a root E0 in [0.84119, 0.84120]
   (exact sign change), refined to width 2^-140 by exact bisection.
3. The eigenvector for E0 in the cyclic subspace is psi = sum_k q_k(E0) K_k with
   P(x)/(x - E0) = sum q_k x^k (unique, since the subspace is cyclic). With the exact Gram
   matrices G_ij = K_i^dag K_j and GR_ij = K_i^dag R^2 K_j (R^2 = squared distance from the
   centre, integer per site), rho^2 = q.GR.q / q.G.q is evaluated in interval arithmetic.
Result: rho = 1.35359703897925225097... sites. That E0 is the lowest positive level of the whole
H is checked in floating point (tools/carrier_mode_exact.py: next level 1.4554).

Usage: python3 tools/carrier_rms_certificate.py   (needs sympy, mpmath; about a minute)
"""
import numpy as np, sympy as sp
from sympy.polys.matrices import DomainMatrix
from sympy import QQ_I, QQ, I, Rational as R
from mpmath import iv, mp
src=open('tools/confined_walk.py').read().split('for n in (3,5):')[0]
exec(src)
n=3; Ns=[]
for j in range(3): M,sites=Nw(n,j,'0'); Ns.append(M)
V=27; Hn=np.kron(np.eye(V),H0)-sum(Ns); N=8*V
def q(z):
    r=sp.Rational(round(z.real*4),4); im=sp.Rational(round(z.imag*4),4)
    assert abs(z-(float(r)+1j*float(im)))<1e-12
    return QQ_I.from_sympy(r+im*I)
H=DomainMatrix([[q(Hn[i,j]) for j in range(N)] for i in range(N)],(N,N),QQ_I)
s0=DomainMatrix([[QQ_I(1) if i==8*13 else QQ_I(0)] for i in range(N)],(N,1),QQ_I)
K=[s0]
for k in range(28): K.append(H*K[-1])
Km=DomainMatrix.hstack(*K)                     # N x 29
c=Km.nullspace().to_Matrix().row(0); c=[sp.nsimplify(ci/c[28]) for ci in c]   # monic degree 28
x=sp.Symbol('x'); P=sp.Poly(sum(c[k]*x**k for k in range(29)),x)
f=sp.Poly(16*x**14 + 16*x**13 - 1376*x**12 - 1136*x**11 + 46000*x**10 + 32480*x**9 - 765352*x**8 - 471624*x**7 + 6728084*x**6 + 3638324*x**5 - 30487536*x**4 - 13950176*x**3 + 63342693*x**2 + 21134505*x - 42629661,x)
assert sp.rem(P,f).is_zero
# isolate E0 to width 1e-40 by exact bisection
lo,hi=R(84119,100000),R(84120,100000); assert f.eval(lo)*f.eval(hi)<0
for _ in range(140):
    mid=(lo+hi)/2
    if f.eval(lo)*f.eval(mid)<=0: hi=mid
    else: lo=mid
# Gram matrices (exact)
d2=[sum((t-1)**2 for t in s) for s in sites]
Wd=DomainMatrix.diag([QQ_I(d2[i//8]) for i in range(N)],QQ_I)
KH=Km.convert_to(QQ_I).to_Matrix().H; KH=DomainMatrix.from_Matrix(KH).convert_to(QQ_I)
G=(KH*Km).to_Matrix(); GR=(KH*Wd*Km).to_Matrix()
mp.dps=60
iv.dps=60
def ivr(r):
    r=sp.Rational(r); return iv.mpf(int(r.p))/iv.mpf(int(r.q))
ci=[ivr(v) for v in c]
Gi=[[ivr(sp.re(G[i,j])) for j in range(28)] for i in range(28)]
GRi=[[ivr(sp.re(GR[i,j])) for j in range(28)] for i in range(28)]
print('Gram imaginary parts zero:', all(sp.im(G[i,j])==0 and sp.im(GR[i,j])==0 for i in range(28) for j in range(28)))
def rho2(E):
    qk=[sum(ci[m]*E**(m-k-1) for m in range(k+1,29)) for k in range(28)]
    num=sum(qk[i]*qk[j]*GRi[i][j] for i in range(28) for j in range(28))
    den=sum(qk[i]*qk[j]*Gi[i][j] for i in range(28) for j in range(28))
    return num/den
E=iv.mpf([ivr(lo).a,ivr(hi).b])
r2=rho2(E)
print('E0 in',sp.Float(lo,20),sp.Float(hi,20))
print('rho^2 in',r2.a,r2.b)
print('rho in', iv.sqrt(r2))
