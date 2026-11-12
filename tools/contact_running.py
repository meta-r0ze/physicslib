#!/usr/bin/env python3
"""Dirac identities behind PMAction.ContactRunning (comparison tool, not a Lean theorem).

Checks, with Paper II's matrices (WallChiralCurrent.diracGamma, gamma5 = Gamma):
  sum g^r g^s G (x) g_r g_s G = 16 G (x) G   (same orientation)
  sum g^r g^s G (x) G g_s g_r = 4 G (x) G    (opposite orientation)
  with G = g^mu P_L contracted over mu, and g^s g^mu g_s = -2 g^mu;
  and the charge assembly c = 2 for the neutron (= (3/2)(1 + 2 Qbar)).
"""
import numpy as np, itertools
I=1j
beta=np.array([[0,0,1,0],[0,0,0,1],[1,0,0,0],[0,1,0,0]],complex)
gam=np.diag([1,1,-1,-1]).astype(complex)
al=[np.array([[0,1,0,0],[1,0,0,0],[0,0,0,-1],[0,0,-1,0]],complex),
    np.array([[0,-I,0,0],[I,0,0,0],[0,0,0,I],[0,0,-I,0]],complex),
    np.diag([1,-1,-1,1]).astype(complex)]
g=[beta]+[beta@a for a in al]; eta=[1,-1,-1,-1]
g5=I*g[0]@g[1]@g[2]@g[3]; print('gammaFive == Gamma:',np.allclose(g5,gam))
PL=(np.eye(4)-g5)/2
low=[eta[m]*g[m] for m in range(4)]
base=sum(np.kron(g[m]@PL,low[m]@PL) for m in range(4))
same=sum(np.kron(g[r]@g[s]@g[m]@PL, low[r]@low[s]@low[m]@PL) for r,s,m in itertools.product(range(4),repeat=3))
opp =sum(np.kron(g[r]@g[s]@g[m]@PL, low[m]@low[s]@low[r]@PL) for r,s,m in itertools.product(range(4),repeat=3))
for name,X in [('same',same),('opp',opp)]:
  c=np.vdot(base,X)/np.vdot(base,base); print(name,'= %.6f * base'%c.real, 'exact:',np.allclose(X,c*base))
contr=[sum(g[s]@g[m]@low[s] for s in range(4)) for m in range(4)]
print('g^s g^m g_s = -2 g^m:',all(np.allclose(contr[m],-2*g[m]) for m in range(4)))
# charge assembly
from fractions import Fraction as F
def c(Q1,Q2,Q3,Q4): return -F(1,2)*(Q1-Q2)**2-F(1,2)*(Q3-Q4)**2-4*(Q1*Q3+Q2*Q4)+(Q1*Q4+Q2*Q3)
print('neutron c =',c(F(2,3),F(-1,3),F(-1),F(0)),' target (3/2)(1+2Qbar) =',F(3,2)*(1+2*(F(2,3)+F(-1,3))/2))
