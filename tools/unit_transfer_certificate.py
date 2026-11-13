#!/usr/bin/env python3
"""Certificate for a unit-transfer history (PMConstants REVIEW, strong CP; the premise of
`SubstrateCharge.theta_zero_substrate`).

The history operator is the Hermitian Wilson kernel H_W = g5 (D_W - M) at the Wilson point
M = r = 1 of `PMAction.DomainWall`, on an L^4 torus, with the gauge field entering through the link
transports on the hop (`PMAction.Machine.MatterContinuum`: the spinor hop with links is the
covariant Dirac term). The background is a constant U(1) field inside the colour group with n12
flux quanta through the (0,1) planes and n34 through the (2,3) planes, topological charge
n12 * n34.

Rigorous (python-flint ball arithmetic, 128 bits; floating point only proposes Q):
1. Link phases exp(2 pi i f), f an exact rational, are arb balls; H is an acb ball matrix that
   contains the exact operator.
2. Q is a floating eigenbasis. B = Q^H H Q and G = Q^H Q - I are computed in ball arithmetic.
   ||G||_F < 1 makes Q invertible, so inertia(H) = inertia(B) (Sylvester's law of inertia).
3. B is Hermitian; its eigenvalues lie within ||B - diag B||_F of its real diagonal (Weyl). If
   every |Re B_ii| exceeds that bound, the number of negative diagonal entries is exactly the
   number of negative eigenvalues of H, and H is invertible.

Result (L = 3, dimension 324): the trivial history has 162 filled modes, the unit history
(n12, n34) = (1, -1) has 163, both invertible (smallest |Re B_ii| 1.0 and 0.3455 against
off-diagonal bounds below 3e-13). L = 4 (dimension 1024): 512 and 513, gap 0.6192. Floating-point
exploration also gives index n12 * n34 for (1,1), (1,0), (2,1).

Usage: python3 tools/unit_transfer_certificate.py [L]   (needs numpy, python-flint; L = 3 takes
a few seconds, L = 4 under a minute)
"""
import numpy as np, itertools, sys, time
from fractions import Fraction as Fr
import flint
flint.ctx.prec = 128

def gammas():
    I=1j
    s=[np.array([[0,1],[1,0]]),np.array([[0,-I],[I,0]]),np.array([[1,0],[0,-1]])]
    Z=np.zeros((2,2)); E=np.eye(2)
    g=[np.block([[Z,-I*x],[I*x,Z]]) for x in s]+[np.block([[Z,E],[E,Z]])]
    return [m.astype(complex) for m in g], (g[0]@g[1]@g[2]@g[3]).astype(complex)

def phases(L,n12,n34):
    """link phase / (2 pi) as exact fractions"""
    P={}
    for x in itertools.product(range(L),repeat=4):
        for mu in range(4): P[(mu,x)]=Fr(0)
        for (a,b,n) in [(0,1,n12),(2,3,n34)]:
            P[(b,x)]+=Fr(n*x[a],L*L)
            if x[a]==L-1: P[(a,x)]-=Fr(n*x[b],L)
    return P

def build(L,n12,n34,M=1,r=1):
    g,g5=gammas(); N=L**4; n=4*N
    idx=lambda x: np.ravel_multi_index(x,(L,)*4)
    P=phases(L,n12,n34)
    # D as dict of blocks with exact Gaussian-integer/2 spin coefficients times a phase
    Df=np.zeros((n,n),complex)
    entries={}  # (i,j) -> list of (coef complex exact (halves), phase Fraction)
    def add(i,j,blk,ph):
        for a in range(4):
            for b in range(4):
                c=blk[a,b]
                if c!=0: entries.setdefault((4*i+a,4*j+b),[]).append((c,ph))
    for x in itertools.product(range(L),repeat=4):
        i=idx(x); add(i,i,(4*r-M)*np.eye(4),Fr(0))
        for mu in range(4):
            xp=list(x); xp[mu]=(xp[mu]+1)%L; j=idx(tuple(xp)); ph=P[(mu,x)]
            add(i,j,-0.5*(r*np.eye(4)-g[mu]),ph)
            add(j,i,-0.5*(r*np.eye(4)+g[mu]),-ph)
    # H = (I_N x g5) D : row block i gets g5 applied
    Hf=np.zeros((n,n),complex); Hb={}
    for (p,q),lst in entries.items():
        i,a=divmod(p,4)
        for a2 in range(4):
            c5=g5[a2,a]
            if c5==0: continue
            for c,ph in lst:
                cc=c5*c
                Hf[4*i+a2,q]+=cc*np.exp(2j*np.pi*float(ph))
                Hb.setdefault((4*i+a2,q),[]).append((cc,ph))
    return Hf,Hb,n

def ball(c):
    re=flint.arb(flint.fmpq(Fr(c.real).limit_denominator(4).numerator,Fr(c.real).limit_denominator(4).denominator))
    im=flint.arb(flint.fmpq(Fr(c.imag).limit_denominator(4).numerator,Fr(c.imag).limit_denominator(4).denominator))
    assert abs(Fr(c.real).limit_denominator(4)-c.real)<1e-15 and abs(Fr(c.imag).limit_denominator(4)-c.imag)<1e-15
    return flint.acb(re,im)

def certify(L,n12,n34):
    t=time.time()
    Hf,Hb,n=build(L,n12,n34)
    assert np.allclose(Hf,Hf.conj().T)
    w,Q=np.linalg.eigh(Hf)
    cache={}
    def ph(f):
        if f not in cache: cache[f]=flint.acb(flint.fmpq(2*f.numerator,f.denominator)).exp_pi_i()
        return cache[f]
    H=flint.acb_mat(n,n)
    for (p,q),lst in Hb.items():
        s=flint.acb(0)
        for c,f in lst: s+=ball(c)*ph(f)
        H[p,q]=s
    Qb=flint.acb_mat([[flint.acb(float(Q[i,j].real),float(Q[i,j].imag)) for j in range(n)] for i in range(n)])
    QH=Qb.conjugate().transpose()
    B=QH*H*Qb
    G=QH*Qb-flint.acb_mat(n,n,[1 if i==j else 0 for i in range(n) for j in range(n)])
    gF=flint.arb(0); eF=flint.arb(0); neg=0; dmin=None
    for i in range(n):
        for j in range(n):
            gF+=abs(G[i,j])**2
            if i!=j: eF+=abs(B[i,j])**2
    gF=gF.sqrt(); eF=eF.sqrt()
    for i in range(n):
        d=B[i,i].real
        m=abs(d)-eF
        assert m>0, (i,d,eF)
        if d<0: neg+=1
        dmin=abs(d) if dmin is None or abs(d)<dmin else dmin
    assert gF<1
    print(f"L={L} flux=({n12},{n34}) dim={n} negCount={neg} (half={n//2}) "
          f"min|diag|={float(dmin.mid()):.4f} offdiag_F<={float(eF.upper()):.2e} ||QhQ-I||_F<={float(gF.upper()):.2e} "
          f"[{time.time()-t:.0f}s]")
    return neg

if __name__=="__main__":
    L=int(sys.argv[1]) if len(sys.argv)>1 else 3
    a=certify(L,0,0); b=certify(L,1,-1)
    assert b==a+1
    print("certified: unit-flux history has exactly one more filled mode than the trivial one")
