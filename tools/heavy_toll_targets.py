#!/usr/bin/env python3
"""Comparison diagnostic only, not a derivation input (SM-inspired; data enter at e8p).

Heavy-label Toll differences implied by recorded mass ratios under s = exp(-T/2) (PMAction.TollAmplitude).

External, numerical. For each mass-ratio convention, find the heavy weight s on the derived wire
(k = alpha/2, resonance delta = -1; as tools/protocol_readout_scan.py) and print the Toll
differences T_e - T_d = 2 ln(s_d/s_e), T_d - T_u = 2 ln(s_u/s_d).
Any Toll linear in the static hypercharge tag (e -6, d -2, u 4) predicts the ratio
(T_d - T_u)/(T_e - T_d) = 6/4 = 3/2 with no free parameter.
The implied values depend on the quark-mass scale convention. A derived schedule is compared
with them afterwards; they do not select it.
"""
import numpy as np
from scipy.optimize import brentq
a=1/137.035999; k=a/2
def m23(s):
    X=-np.eye(3,dtype=complex); X[1,0]+=1;X[2,1]+=1;X[0,2]+=1
    sv=np.sort(np.linalg.svd(np.diag([s,k,k])@X@np.diag([s,1,1]),compute_uv=False)); return sv[1]/sv[2]
def s_of(t):
    ss=np.logspace(-3,3,4000); v=[m23(x)-t for x in ss]
    for i in range(len(ss)-1):
        if v[i]*v[i+1]<0: return brentq(lambda x:m23(x)-t,ss[i],ss[i+1])
lep=206.768/3477
for lab,d,u in [("library ledger (m_s(2GeV)/m_b(m_b), m_c(m_c)/m_t)",93.54/4181.6,1267.25/172671),
                ("PDG mixed (scan)",0.0199,0.00372),("M_Z running (scan)",0.0187,0.0036),("scan 'own scale'",0.0223,0.0042)]:
    se,sd,su=s_of(lep),s_of(d),s_of(u)
    Ted=2*np.log(sd/se); Tdu=2*np.log(su/sd)
    print(f"{lab:52s} T_e-T_d={Ted:.3f} T_d-T_u={Tdu:.3f} ratio={Tdu/Ted:.3f} (hypercharge-linear: 1.500)")
