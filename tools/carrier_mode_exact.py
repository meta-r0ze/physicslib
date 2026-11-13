#!/usr/bin/env python3
"""The confined carrier's ground mode in exact arithmetic (toward PMAction REVIEW A.1).

H = I (x) H0 - sum_j N_j on the 3^3 cube (ConfinedCarrier, plain truncation) has entries in
Q(i). The Krylov space of H from one spinor component on the centre site is 28-dimensional and
contains the spin-up ground mode. Its minimal polynomial (exact, Gaussian rationals) factors over
Q into two degree-14 integer polynomials p(x), p(-x); the ground energy E0 = 0.8411986 is the
smallest positive root of p(-x), certified here by a sign change on [0.84119, 0.84120]. Also
prints the ground mode's weight on the centre, faces, edges and corners, and the rms radius
rho^2 = W1 + 2 W2 + 3 W3 = 1.8322 (rho = 1.3536 sites).

Usage: python3 tools/carrier_mode_exact.py   (needs sympy)
"""
import numpy as np, sympy as sp
from sympy.polys.matrices import DomainMatrix
from sympy import QQ_I, I
src=open('tools/confined_walk.py').read().split('for n in (3,5):')[0]
exec(src)
n=3; Ns=[]
for j in range(3): M,sites=Nw(n,j,'0'); Ns.append(M)
V=27; Hn=np.kron(np.eye(V),H0)-sum(Ns)
def q(z):
    r=sp.nsimplify(round(z.real*4)/4); im=sp.nsimplify(round(z.imag*4)/4)
    assert abs(z-(float(r)+1j*float(im)))<1e-12
    return QQ_I.from_sympy(r+im*I)
N=8*V
H=DomainMatrix([[q(Hn[i,j]) for j in range(N)] for i in range(N)],(N,N),QQ_I)
s0=[QQ_I(0)]*N; s0[8*13+0]=QQ_I(1)
vecs=[DomainMatrix([[x] for x in s0],(N,1),QQ_I)]
for k in range(29): vecs.append(H*vecs[-1])
K=DomainMatrix.hstack(*vecs[:29])   # N x 29
# solve K c = 0 for kernel: minimal relation
ker=K.nullspace()
print('kernel dim',ker.shape)
c=ker.to_Matrix().row(0)
x=sp.Symbol('x'); poly=sp.Poly(sum(c[i]*x**i for i in range(29)),x)
print(sp.factor_list(poly.as_expr()))

# the two degree-14 factors; the ground energy is the smallest positive root of p(-x)
p=sp.Poly(16*x**14 - 16*x**13 - 1376*x**12 + 1136*x**11 + 46000*x**10 - 32480*x**9 - 765352*x**8 + 471624*x**7 + 6728084*x**6 - 3638324*x**5 - 30487536*x**4 + 13950176*x**3 + 63342693*x**2 - 21134505*x - 42629661,x)
for f in (p, sp.Poly(p.as_expr().subs(x,-x),x)):
    r=[complex(z) for z in sp.Poly(f).nroots(n=20)]
    print('real roots',sorted(round(z.real,6) for z in r if abs(z.imag)<1e-12))
lo,hi=sp.Rational(84119,100000),sp.Rational(84120,100000)
for f in (p, sp.Poly(p.as_expr().subs(x,-x),x)):
    print('sign change on [0.84119,0.84120]:', f.eval(lo)*f.eval(hi)<0)

# --- floating-point weights by orbit ---
src=open('tools/confined_walk.py').read().split('for n in (3,5):')[0]
exec(src)
n=3; Ns=[]
for j in range(3): M,sites=Nw(n,j,'0'); Ns.append(M)
V=27; H=np.kron(np.eye(V),H0)-sum(Ns)
w,Vv=np.linalg.eigh(H); pos=w>1e-9
print('lowest positive levels', np.round(sorted(set(np.round(w[pos],6)))[:6],6))
e0=w[pos].min(); print('E0',repr(e0), 'multiplicity', np.isclose(w,e0,atol=1e-8).sum())
# minimal polynomial guess via char poly of H restricted? try findpoly on E0 high precision via refining
# distances / weights by orbit
sub=Vv[:,np.isclose(w,e0,atol=1e-8)]
dens=(abs(sub)**2).sum(1).reshape(V,8).sum(1)/sub.shape[1]
cls={}
for i,x in enumerate(sites):
    d2=sum((q-1)**2 for q in x); cls.setdefault(d2,[]).append(dens[i])
for d2 in sorted(cls): print('d^2',d2,'sites',len(cls[d2]),'weight each %.5f total %.5f'%(cls[d2][0],sum(cls[d2])))
