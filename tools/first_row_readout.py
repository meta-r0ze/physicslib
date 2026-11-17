"""First-row deficit as wall leakage, with the G_F calibration (EP REVIEW, first-row item).

Each protocol has its own two-wall wire (tools/event_clock_check.py model; weight s and off-resonance
offset eps from EP OVERVIEW's fits). The charged current is P_L = keep the Gamma = -1 components (b, d),
times a generation rotation V (measured CKM, PMFlavor's). F = fraction of P_L V psi (parent light mode)
on the daughter's light subspace. The row is measured against G_F from muon decay, so the deficit is
1 - F_u / F_mu (u row against mu -> nu). Results: the deficit is ~0.25 r^2 with the fitted weights, so
this leakage adds to PMFlavor's 1/516 dressing (the deficit's source,
PMFlavor.DressingInheritance), so with the measured 1.6 +/- 0.7 e-3 it bounds r <~ 0.07 (2 sigma); it depends on the fitted weights by a factor ~3
(equal weights: 1.3e-3 at r = 1/8 against 3.9e-3).
"""
import numpy as np
a=1/137.035999; k=a/2
def H(r,s,d=-1.0):
    D1=r*np.diag([s,k,k]).astype(complex)
    X=d*np.eye(3,dtype=complex); X[1,0]+=1; X[2,1]+=1; X[0,2]+=1
    D2=r*X@np.diag([s,1,1]); Z=np.zeros((3,3)); Y=np.eye(3)
    return np.block([[Z,D1,Z,Z],[D1.conj().T,Z,-Y,Z],[Z,-Y,Z,D2],[Z,Z,D2.conj().T,Z]])
PL=np.diag([0]*3+[1]*3+[0]*3+[1]*3).astype(complex)
def ckm():
    s12,s23,s13=0.2250,0.0418,0.00369
    c12,c23,c13=[np.sqrt(1-x*x) for x in (s12,s23,s13)]
    R23=np.array([[1,0,0],[0,c23,s23],[0,-s23,c23]]);R13=np.array([[c13,0,s13],[0,1,0],[-s13,0,c13]]);R12=np.array([[c12,s12,0],[-s12,c12,0],[0,0,1]])
    return R23@R13@R12
lift=lambda G: np.kron(np.eye(4),G)
def light(r,s,eps):
    E,V=np.linalg.eigh(H(r,s,-1+eps)); o=np.argsort(abs(E))[:6]
    P=sum(np.outer(V[:,i],V[:,i].conj()) for i in o)
    pos=sorted([i for i in o if E[i]>0],key=lambda i:E[i])
    return P,[V[:,i] for i in pos],E[pos]
def frac(ps,pe,gen,ds,de,r,Vg):
    _,vp,Ep=light(r,ps,pe); Pd,_,_=light(r,ds,de)
    J=PL@lift(Vg)@vp[gen]
    return (np.vdot(J,Pd@J).real)/np.vdot(J,J).real, np.vdot(J,J).real
V=ckm()
print("up-row light fraction F_u, muon F_mu; deficit = 1 - F_u/F_mu  (measured 1.6 +/- 0.7 e-3)")
for r in (1/8,1/6,1/4,1/3,1/2):
    Fu,nu=frac(1.14,0.0024,0,0.26,0.14,r,V)
    Fm,nm=frac(0.087,0.038,1,0.030,0.001,r,np.eye(3))
    Fe,ne=frac(0.087,0.038,0,0.030,0.001,r,np.eye(3))
    print(f"r={r:.3f}: F_u={Fu:.5f} F_mu={Fm:.5f} F_e={Fe:.5f}  deficit={1-Fu/Fm:.2e}   (|P_L psi|^2: u {nu:.3f} mu {nm:.3f})")
print("V = identity (no mixing):")
for r in (1/16,1/12,1/8,1/4):
    Fu,_=frac(1.14,0.0024,0,0.26,0.14,r,np.eye(3)); Fm,_=frac(0.087,0.038,1,0.030,0.001,r,np.eye(3))
    FuV,_=frac(1.14,0.0024,0,0.26,0.14,r,V)
    print(f"r={r:.4f}: deficit V=1 {1-Fu/Fm:.2e}, V=CKM {1-FuV/Fm:.2e}, ratio to r^2: {(1-FuV/Fm)/r**2:.3f}")
# sensitivity to weights/offsets: up with s_u=1 eps=0, down s=1 eps small
for (su,eu,sd,ed) in ((1.0,0.001,1.0,0.001),(1.14,0.0024,0.26,0.14),(1.14,0.0024,0.26,0.01)):
    Fu,_=frac(su,eu,0,sd,ed,1/8,V); Fm,_=frac(0.087,0.038,1,0.030,0.001,1/8,np.eye(3))
    print(f"s_u={su} eps_u={eu} s_d={sd} eps_d={ed}: deficit at r=1/8 {1-Fu/Fm:.2e}")
