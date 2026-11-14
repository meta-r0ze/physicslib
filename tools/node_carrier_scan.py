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

Findings (grid over d of both signs; a sample, not a bound):
1. For fixed k the pair (heavy/middle, middle/light) runs along a one-parameter curve in d. One
   free parameter for two ratios, so each sector is a test.
2. Down quarks (M_Z: 52, 19) with k = alpha/2: best d = 0.025 gives (47.8, 18.9), within 9% on both
   ratios. With k = alpha: (43.4, 18.9), within 19%.
3. Up quarks (277, 488) and charged leptons (16.8, 207): the curve misses. Best points are
   (45.4, 476) for up (heavy/middle about 6x low) and (5.6, 223) for leptons (about 3x low). The
   total hierarchy is not the obstruction (the curve reaches larger totals); the shape is. Up and
   leptons need light carriers other than the equal-magnitude node rule gives.
4. required_k: solving (k, d) exactly for each sector's two ratios (two branches each): down
   k = 0.00338 or 0.0059 (alpha/2 = 0.00365 is 7% from the first); up k = 8.8e-5 or 3.0e-4
   (12-40x below alpha/2); leptons k = 0.0011-0.0013 or 0.0145-0.0166 (5-80x below sqrt(alpha)).
   Up and leptons need an extra suppression of the light carrier that the library does not supply.
5. down_rotation: at the down fit point (k = alpha/2, d = 0.0251) the left rotation has no free
   parameters. The heavy state is the label-v generation (0.990); the rotation angles are about
   0.16 (light-middle), 0.14 (middle-heavy), 0.024 (light-heavy). The CKM is U_u^T U_d, so this is
   not the CKM by itself; it shows the wire's mass carries Cabibbo-size mixing, and the up rotation
   must cancel most of the 0.14 to reach |V_cb| = 0.041.
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

def required_k(seed=0, starts=400):
    from scipy.optimize import least_squares
    rng = np.random.default_rng(seed)
    for sec, t in DATA.items():
        sols = set()
        for sign in (1, -1):
            for _ in range(starts):
                f = lambda p: np.log(ratios(10 ** p[0], sign, p[1])) - np.log(t)
                r = least_squares(f, [rng.uniform(-6, 0), rng.uniform(-1, 1)])
                if r.cost < 1e-10:
                    sols.add((round(10 ** r.x[0], 6), round(abs(r.x[1]), 5)))
        print(sec, "required (k, |d|):", sorted(sols))

def down_rotation(d=0.0251):
    U, s, _ = np.linalg.svd(mass(1.0, ALPHA / 2, ALPHA / 2, d)); o = np.argsort(s)
    print("down rotation |U| (rows v, s, c; columns light, middle, heavy):")
    print(np.round(np.abs(U[:, o]), 4))

if __name__ == "__main__":
    required_k()
    down_rotation()
    D = np.concatenate([-np.logspace(-6, 2, 4000), np.logspace(-6, 2, 4000)])
    for sec, (r1, r2) in DATA.items():
        for name, k in CASES[sec]:
            best = min(((abs(np.log(a / r1)) + abs(np.log(b / r2)), d, a, b)
                        for d in D for a, b in [ratios(k, 1, d)]), key=lambda t: t[0])
            hmax = max(a * b for d in D for a, b in [ratios(k, 1, d)])
            print(f"{sec:8s} k={name:12s} max total hierarchy {hmax:9.0f}  data total {r1 * r2:9.0f}"
                  f"  best d {best[1]:+.4f} -> ({best[2]:.1f}, {best[3]:.1f}) vs ({r1}, {r2})")
