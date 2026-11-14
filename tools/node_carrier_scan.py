"""External scan (not a proof): the reference-wall light mass of PMFlavor.ReferenceWallMass,
M = diag(K, k_s, k_c)(d + C), with the carrier amplitudes fixed by the node rules instead of fitted.

Inputs from the library (no tuning):
* K = 1: the label-v generation's carrier is vector class, in-cycle (ExchangeAxis), the unit.
* |k_s| = |k_c| = k on both walls: spinor carriers pass the node on either wall
  (LeptonAxisRestriction.cycle_root_axis_zero acts on both sectors), and every leg has the same
  weight (HandoffAdmittance.closure_one_price). The weak repair negates the left sector only
  (LeptonAxisRestriction.weak_type): a relative sign, not a magnitude. Both signs are scanned
  (they map to d -> -d).
* k from NodeElimination / KronSeries: quarks two legs, alpha/2 (Kron series) or alpha (bare);
  leptons one leg, sqrt(alpha).
* d, the other wall's on-site detuning relative to K: the one free parameter per sector.

Findings:
1. For fixed k the pair (heavy/middle, middle/light) runs along a one-parameter curve in d, and the
   total hierarchy m_heavy/m_light has a maximum (about 1000 for k = alpha/2, about 140 for
   k = sqrt(alpha)).
2. Down quarks (M_Z: 52, 19; total 988) with k = alpha/2: best d = 0.025 gives (47.8, 18.9), within
   9% on both ratios, near the curve's maximum hierarchy. With k = alpha: within 19%.
3. Up quarks (277, 488; total about 135000) and charged leptons (16.8, 207; total about 3500) exceed
   the maximum hierarchy for any d: excluded for this form. They need smaller or unequal light
   carriers than the equal-magnitude node rule gives.
"""
import numpy as np

ALPHA = 1 / 137.036
DATA = {"leptons": (16.8, 207.0), "down": (52.0, 19.0), "up": (277.0, 488.0)}
CASES = {"leptons": [("sqrt(alpha)", np.sqrt(ALPHA))],
         "down": [("alpha", ALPHA), ("alpha/2", ALPHA / 2)],
         "up": [("alpha", ALPHA), ("alpha/2", ALPHA / 2)]}

def mass(K, ks, kc, d):
    C = np.zeros((3, 3)); C[1, 0] = K; C[2, 1] = kc; C[0, 2] = ks
    return np.diag([K, ks, kc]) @ (d * np.eye(3) + C)

def ratios(k, sign, d):
    s = np.sort(np.linalg.svd(mass(1.0, k, sign * k, d), compute_uv=False))[::-1]
    return s[0] / s[1], s[1] / s[2]

if __name__ == "__main__":
    D = np.concatenate([-np.logspace(-6, 2, 4000), np.logspace(-6, 2, 4000)])
    for sec, (r1, r2) in DATA.items():
        for name, k in CASES[sec]:
            best = min(((abs(np.log(a / r1)) + abs(np.log(b / r2)), d, a, b)
                        for d in D for a, b in [ratios(k, 1, d)]), key=lambda t: t[0])
            hmax = max(a * b for d in D for a, b in [ratios(k, 1, d)])
            print(f"{sec:8s} k={name:12s} max total hierarchy {hmax:9.0f}  data total {r1 * r2:9.0f}"
                  f"  best d {best[1]:+.4f} -> ({best[2]:.1f}, {best[3]:.1f}) vs ({r1}, {r2})")
