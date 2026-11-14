"""Superseded form: this scan assumes equal on-site detuning on both walls. PMAction.ReferenceDetuning
puts it to zero on the reference's wall, and PMFlavor.ReferenceWallMass gives M = D_R (d + cyc k_O)
instead; findings 1 and 4 below do not apply to that form.

External scan (not a proof): singular values of the composite light mass of
PMFlavor.CompositeMass, up to the overall scale delta/y:

    A = d * S + diag(k_v, k_1, k_2),   S the reverse 3-cycle (cycInv with y = 1),

with k_v = 1 the heavy (label-v) carrier, k_1, k_2 the light (spinor, node-suppressed) carriers,
d = delta (on-site chirality flip) relative to k_v. Amplitudes are real (no phase source:
DomainWall's crossing is the real hop, CarrierFlip gives kappa = -t/2).

Findings (seeded random samples; a sample, not a bound):
1. k_1 = k_2 (the composite's order), positive, k_light <= k_v: (m/l)/(h/m) <= 1, the maximum at
   the geometric limit s ~ (k_v, d, d^2/k_v). Leptons (16.8, 207) and up quarks at M_Z (277, 488)
   need (m/l)/(h/m) > 1: excluded. Down (54, 20) is allowed.
2. k_1 != k_2: every sector is reachable (three parameters, two ratios: no test). The required
   light-carrier ratios are about 1e5 (leptons), 6e3 (up), 20 (down).
4. min_split: the smallest ratio of the two light diagonal entries that fits each sector
   (grid, log error < 0.04): leptons about 200, up (M_Z) about 500, down 1. With
   PMFlavor.LightSplit.near_maximal both wall asymmetries must be near maximal for leptons and up.
3. Signed or complex amplitudes reach large ratios only by cancelling det A = k_v k_1 k_2 + d^3.
"""
import numpy as np

S = np.zeros((3, 3)); S[0, 1] = S[1, 2] = S[2, 0] = 1
DATA = {"leptons": (16.8, 207.0), "down": (54.0, 20.0), "up (M_Z)": (277.0, 488.0)}

def ratios(d, k1, k2):
    s = np.linalg.svd(d * S + np.diag([1.0, k1, k2]), compute_uv=False)
    return s[0] / s[1], s[1] / s[2]

def max_q(equal, n=300000, seed=1):
    rng = np.random.default_rng(seed); best, arg = 0.0, None
    for _ in range(n):
        d = 10 ** rng.uniform(-6, 0); k1 = 10 ** rng.uniform(-8, 0)
        k2 = k1 if equal else 10 ** rng.uniform(-8, 0)
        r1, r2 = ratios(d, k1, k2)
        if r2 / r1 > best: best, arg = r2 / r1, (d, k1, k2, r1, r2)
    return best, arg

def closest(target, n=400000, seed=2):
    rng = np.random.default_rng(seed); best, arg = 9.0, None
    for _ in range(n):
        d = 10 ** rng.uniform(-6, 0); k1 = 10 ** rng.uniform(-8, -1); k2 = 10 ** rng.uniform(-8, -1)
        r1, r2 = ratios(d, k1, k2)
        dist = abs(np.log(r1 / target[0])) + abs(np.log(r2 / target[1]))
        if dist < best: best, arg = dist, (d, k1, k2, r1, r2)
    return best, arg

def min_split(qs=(1, 10, 100, 200, 300, 500, 700, 1000)):
    D = 10 ** np.linspace(-6, 0, 241); K = 10 ** np.linspace(-8, 0, 321)
    dd, kk = np.meshgrid(D, K, indexing="ij")
    for q in qs:
        A = np.zeros(dd.shape + (3, 3)); A[..., 0, 1] = A[..., 1, 2] = A[..., 2, 0] = dd
        A[..., 0, 0] = 1; A[..., 1, 1] = kk; A[..., 2, 2] = kk / q
        s = np.linalg.svd(A, compute_uv=False); r1, r2 = s[..., 0] / s[..., 1], s[..., 1] / s[..., 2]
        errs = {n: float((np.abs(np.log(r1 / t[0])) + np.abs(np.log(r2 / t[1]))).min())
                for n, t in DATA.items()}
        print("light-entry ratio", q, {n: round(e, 3) for n, e in errs.items()})

if __name__ == "__main__":
    min_split()
    print("equal light carriers, max (m/l)/(h/m):", max_q(True))
    for name, (r1, r2) in DATA.items():
        print(f"{name}: data (m/l)/(h/m) = {r2 / r1:.3g}; unequal-carrier closest:", closest((r1, r2)))
