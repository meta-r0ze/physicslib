"""External fit (not a proof): masses and CKM magnitudes from the reference-wall light mass of
PMFlavor.ReferenceWallMass,

    M = diag(K, k_s, k_c) (d 1 + C),  C[1,0] = K, C[2,1] = k_c, C[0,2] = k_s,

row g carrying generation g's label-class carrier on the reference's wall (g = 0 label v, the heavy
one), C the other wall's carriers at (h + 1, h) with the swap x exchange symmetry
(k_O(v) = K, k_O(s) = k_c, k_O(c) = k_s), d the other wall's on-site detuning; K = 1 sets the
scale. Real amplitudes, every sign pattern. Data: masses at M_Z (u 0.00127, c 0.619, t 171.7;
d 0.0029, s 0.055, b 2.86), |V_us| 0.2245, |V_cb| 0.0410, |V_ub| 0.00382. The CKM is
|U_u^T U_d| from the left singular vectors ordered by mass.

Findings (seeded multistart least squares on logs; a sample, not a bound):
1. Carriers universal across up and down (only d differs): 4 parameters, 7 observables. Best fit
   misses by factors up to 2.8 (|V_ub|) and about 1.8 on the down mass ratios: disfavoured.
2. Carriers per sector: 6 parameters, 7 observables. Fits within about 30% (running masses are
   scale-dependent at that level), so the form is consistent but this is nearly a fit, not a test.
A test needs the carrier amplitudes derived (the node-passage cost per wall).
"""
import sys, itertools
import numpy as np
from scipy.optimize import least_squares

UP = np.array([0.00127, 0.619, 171.7]); DN = np.array([0.0029, 0.055, 2.86])
CKM = np.array([0.2245, 0.0410, 0.00382])
TARGET = np.log(np.r_[UP[1] / UP[0], UP[2] / UP[1], DN[1] / DN[0], DN[2] / DN[1], CKM])

def mass(K, ks, kc, d):
    C = np.zeros((3, 3)); C[1, 0] = K; C[2, 1] = kc; C[0, 2] = ks
    return np.diag([K, ks, kc]) @ (d * np.eye(3) + C)

def sector(*a):
    U, s, _ = np.linalg.svd(mass(*a)); o = np.argsort(s); return s[o], U[:, o]

def observables(v, universal):
    if universal: ks, kc, du, dd = v; ksd, kcd = ks, kc
    else: ks, kc, du, ksd, kcd, dd = v
    su, Uu = sector(1, ks, kc, du); sd, Ud = sector(1, ksd, kcd, dd); V = np.abs(Uu.T @ Ud)
    return np.log(np.r_[su[1] / su[0], su[2] / su[1], sd[1] / sd[0], sd[2] / sd[1],
                        V[0, 1], V[1, 2], V[0, 2]] + 1e-300)

def fit(universal, starts, seed=3):
    n = 4 if universal else 6; rng = np.random.default_rng(seed); best = (np.inf, None, None)
    for sg in itertools.product([1, -1], repeat=n):
        sg = np.array(sg)
        for _ in range(starts):
            r = least_squares(lambda p: observables(10 ** p * sg, universal) - TARGET,
                              rng.uniform(-6, 1, n), bounds=(-9, 3))
            if r.cost < best[0]: best = (r.cost, r.x, sg)
    cost, x, sg = best
    print("universal" if universal else "per-sector", "cost", cost, "log10|params|", np.round(x, 3),
          "signs", sg, "fit/data", np.round(np.exp(observables(10 ** x * sg, universal) - TARGET), 3))

if __name__ == "__main__":
    fit(True, 40); fit(False, 12)
