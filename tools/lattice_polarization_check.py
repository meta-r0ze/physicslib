#!/usr/bin/env python3
"""External numeric check (not a proof) for PMAction's "Subtracted lattice polarization" item.

Lattice integrand (PMAction.PolarizationContact): bubble leg_mu leg_nu / (S(k) S(k+q)) minus
contact_mu_nu / S(k), with the sinc-weighted midpoint leg and the q-dependent contact; S is
LeadingLog.symbol over the 24 D4 roots at spacing a. Continuum: (2k+q)_mu (2k+q)_nu / (k^2 (k+q)^2)
minus the seagull 2 delta / k^2. Both are subtracted at q = 0 and integrated over the shell
lo < |k| < hi with the same quasi-Monte-Carlo points (Sobol, log-uniform radius), so quadrature error
cancels in the difference. The q^2 coefficient is extracted by Richardson on (q, q/2).

Findings (lo = 0.02, hi = 0.2):
1. lattice minus continuum q^2 coefficient: +5.43e-2, +1.36e-2, +3.40e-3 at a = 1, 1/2, 1/4:
   exactly a^2 scaling, C a^2 (hi^2 - lo^2) with C about 1.37 (mu = nu = 1, q along e_0). The
   difference is independent of q, so a bound of this form resolves the q^2 coefficient.
2. At O(a^2) the correction is not proportional to the transverse structure q^2 delta - q q (its
   ratio to the projector varies 0.004 to 0.030 over components for q along (1,2,0,1)): the
   lattice breaks rotation symmetry at that order, so the bound is component-wise.
3. The sinc factors of the contact term matter at that order (without them the a = 1/2 difference
   is 8.2e-3 instead of 1.36e-2): the q-dependent contact is needed.

Usage: python3 tools/lattice_polarization_check.py [lo hi log2_points]   (needs numpy, scipy)
"""
import numpy as np, itertools, sys
from scipy.stats import qmc
# D4 roots: +-e_i +- e_j
R=[]
for i,j in itertools.combinations(range(4),2):
    for si in (1,-1):
        for sj in (1,-1):
            v=np.zeros(4); v[i]=si; v[j]=sj; R.append(v)
R=np.array(R)                     # 24 x 4
def S(k,a):                        # symbol, k: N x 4
    x=a*(k@R.T); return (1-np.cos(x)).sum(1)/(6*a*a)
def sinc(x): return np.sinc(x/np.pi)
def leg(k,q,v,a):                  # midpoint, side=1
    rq=a*(R@q)/2; rk=a*(k@R.T)
    return ((R@v)*sinc(rq)*np.sin(rk+rq)).sum(1)/(6*a)
def contact(k,q,u,v,a):
    rq=a*(R@q)/2; rk=a*(k@R.T)
    return (np.cos(rk)*(R@u)*sinc(rq)*(R@v)*sinc(rq)).sum(1)/6
def lat(k,q,mu,nu,a):
    e=np.eye(4)
    return leg(k,q,e[mu],a)*leg(k,q,e[nu],a)/(S(k,a)*S(k+q,a)) - contact(k,q,e[mu],e[nu],a)/S(k,a)
def cont(k,q,mu,nu):
    k2=(k*k).sum(1); kq2=((k+q)**2).sum(1)
    return (2*k[:,mu]+q[mu])*(2*k[:,nu]+q[nu])/(k2*kq2) - 2*(mu==nu)/k2
def points(lo,hi,n,seed):
    s=qmc.Sobol(5,seed=seed).random(n)
    # radius via log-uniform, direction via normalized gaussian from first 4 dims
    from scipy.special import ndtri
    g=ndtri(np.clip(s[:,:4],1e-12,1-1e-12)); g/=np.linalg.norm(g,axis=1)[:,None]
    t=s[:,4]; r=lo*(hi/lo)**t
    w=2*np.pi**2*r**4*np.log(hi/lo)          # volume element r^3 dr dOmega, dr = r ln(hi/lo) dt, |S^3|=2pi^2
    return g*r[:,None], w/n
def coeff(f,lo,hi,qn,n,seed=0):
    k,w=points(lo,hi,n,seed); mu=nu=1
    q=np.array([qn,0,0,0.])
    vals=[]
    for qq in (q,q/2):
        P=(w*(f(k,qq)-f(k,0*qq))).sum(); vals.append(P/(qq@qq))
    return (4*vals[1]-vals[0])/3      # remove q^4

if __name__ == "__main__":
    lo, hi = (float(sys.argv[1]), float(sys.argv[2])) if len(sys.argv) > 2 else (0.02, 0.2)
    n = 2 ** (int(sys.argv[3]) if len(sys.argv) > 3 else 16)
    exact = -(1 / 3) * 2 * np.pi ** 2 * np.log(hi / lo)
    for a in [1.0, 0.5, 0.25]:
        cl = coeff(lambda k, q: lat(k, q, 1, 1, a), lo, hi, lo / 8, n)
        cc = coeff(lambda k, q: cont(k, q, 1, 1), lo, hi, lo / 8, n)
        print(f"a={a}: lattice {cl:.6f}  continuum (same points) {cc:.6f}  exact continuum {exact:.6f}"
              f"  difference {cl - cc:+.3e}  / (a^2 (hi^2 - lo^2)) = {(cl - cc) / (a * a * (hi * hi - lo * lo)):.3f}")
