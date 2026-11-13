#!/usr/bin/env python3
"""Interval-arithmetic enclosure of the E8 neutron lifetime with the full Fermi factor and the
electron's outer radiative correction (continuum route; PMHadrons REVIEW §0, §2).

Inputs are the E8 bounds already proved in Lean: alpha (PMConstants.Values.alpha_bounds),
E0 = m_n - m_p (NeutronContinuum.cutoff_bounds), m_p (CompositeMasses.proton_value), G_F and
hbar/m_e (Values.fermiME_tight, electronTime_tight). The rate is
  G_F^2 |V_ud|^2 R (1 + 3 g_A^2) f / (2 pi^3),  |V_ud|^2 R = 32/33,  g_A = 5/4,
  f = int_1^E0 F(E) p E (E0-E)^2 [1 + (alpha/2pi) g(E, E0)] dE,
F = 2 pi eta/(1 - e^{-2 pi eta}) (eta = alpha E/p), g = Sirlin's function.
The integral is enclosed by interval evaluation on 60000 subintervals (mpmath.iv); Li2 is
enclosed by its monotonicity; the first 1e-6 above E = 1 is bounded crudely and the last 1e-6
below E0 contributes below 1e-12. Runtime about a minute and a half.

Result: full Fermi factor 922.91-923.06 s; with the outer radiative correction 909.22-909.37 s.
With lambda = (5/4)(1 + delta), delta in the published 1.4-2.6% (arXiv:2202.10439):
871.4-888.7 s (measured 878.4 s).

Usage: python3 tools/neutron_rc_certificate.py   (needs mpmath)
"""
# Interval-arithmetic enclosure of the neutron lifetime with the full Fermi factor and the outer
# radiative correction, E8 inputs.
from mpmath import mp, iv, mpf, polylog, log as mlog
mp.dps=40; iv.dps=40
a=iv.mpf(['0.007297352562','0.007297352563'])
E0=iv.mpf(['2.530988555','2.530988656'])
mp_e=iv.mpf(['1836.152673444','1836.152673445'])
pi=iv.pi
def Li2_iv(u):   # Li2 increasing on [0,1): enclose by endpoint values with margin
    lo=polylog(2,mpf(u.a)); hi=polylog(2,mpf(u.b)); eps=mpf(10)**-35
    return iv.mpf([lo-eps,hi+eps])
def integrand(E, with_rc):
    p=iv.sqrt(E*E-1); b=p/E; x=2*pi*a*E/p
    w=2*pi*a*E*E*(E0-E)**2/(1-iv.exp(-x))         # F(E) p E (E0-E)^2
    if not with_rc: return w
    at=iv.log((1+b)/(1-b))/2
    g=(3*iv.log(mp_e)-iv.mpf(3)/4+4*(at/b-1)*((E0-E)/(3*E)-iv.mpf(3)/2+iv.log(2*(E0-E)))
       -4/b*Li2_iv(2*b/(1+b))+at/b*(2*(1+b*b)+(E0-E)**2/(6*E*E)-4*at))
    return w*(1+a/(2*pi)*g)
def enclose(with_rc, N=60000, d1=mpf('1e-6'), d2=mpf('1e-6')):
    # [1,1+d1]: 0 <= F p E(E0-E)^2 <= (1 + x/2 + x^2/12) pE(E0-E)^2; bound crudely by 2*pi*a*E^2(E0-E)^2/(1-e^-x) <= 2pi a E^2 E0^2/(1-0)*... use generous bound
    E0h=mpf(E0.b)
    head_hi=iv.mpf(2)*pi*a*(1+d1)**2*E0h**2*d1*(1+abs(a)*40)   # crude, with RC factor margin
    s=iv.mpf([0,head_hi.b])
    lo=mpf(1)+d1; hi=mpf(E0.a)-d2
    h=(hi-lo)/N
    for k in range(N):
        I=iv.mpf([lo+k*h, lo+(k+1)*h])
        s+=integrand(I,with_rc)*h
    # tail [E0-d2, E0]: |integrand| <= C (E0-E)^2 |log| small; bound by 1e-12 generously
    s+=iv.mpf(['-1e-12','1e-12'])
    return s
fF=enclose(False); print('f with full Fermi factor in', fF)
fR=enclose(True); print('f with Fermi and outer RC in', fR)

te=iv.mpf(['1.28808866e-21','1.28808867e-21']); G=iv.mpf(['3.0456453e-12','3.0456507e-12'])
for nm,f in (('full Fermi factor',fF),('Fermi + outer radiative correction',fR)):
    t=te*33*iv.pi**3/(91*G**2*f)
    print('%s: tau in [%.2f, %.2f] s'%(nm,float(t.a),float(t.b)))
t=te*33*iv.pi**3/(91*G**2*fR)
for d in ('0.014','0.026'):
    lam=iv.mpf(1.25)*(1+iv.mpf(d))
    tt=t*(1+3*iv.mpf(1.25)**2)/(1+3*lam**2)
    print('  lambda = (5/4)(1+%s): tau in [%.2f, %.2f] s'%(d,float(tt.a),float(tt.b)))
