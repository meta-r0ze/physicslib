"""Flip-to-crossing ratio, wall leakage, and the first-row deficit (EP REVIEW, PMAction extension).

Two-wall wire per WallSeesaw: components a, b (wall 1), c, d (wall 2); flips D1 = r diag(s, k, k)
(reference wall) on a-b, D2 = r (delta + cyc) diag(s, 1, 1) (other wall) on c-d, crossing -y on b-c,
y = 1. r = K_f/|y|. Leakage = weight of a light mode on the gapped components b, c.
Durations: PMAction.ClassBlindFlip.forwardTimes_total: the class-blind flip program is 32 quarter-times
q of the root phase (q = pi/(2 gap(p)), in ticks). A certain event of duration T has rate pi/(2T)
(CertainTransferRate), so r = T_crossing / T_flip, independent of the attempt rate p.
"""
import numpy as np
a = 1/137.035999; k = a/2

def H(r, d=-1.0, s=1.0):
    D1 = r*np.diag([s, k, k]).astype(complex)
    X = d*np.eye(3, dtype=complex); X[1, 0] += 1; X[2, 1] += 1; X[0, 2] += 1
    D2 = r*X@np.diag([s, 1, 1]); Z = np.zeros((3, 3)); Y = np.eye(3)
    return np.block([[Z, D1, Z, Z], [D1.conj().T, Z, -Y, Z], [Z, -Y, Z, D2], [Z, Z, D2.conj().T, Z]])

def leak(r, d=-1.0, s=1.0):
    E, V = np.linalg.eigh(H(r, d, s)); i = np.argsort(abs(E))[::2][:3]
    return [float(np.sum(abs(V[3:9, j])**2)) for j in i]

r0 = 1/32
L = leak(r0)
print("1. leakage / r^2 for light modes (lightest, middle, heaviest) at the resonance:",
      [round(x/r0**2, 3) for x in L])
print("2. the lightest mode leaks ~0: it is the exact zero mode (PMAction.ExactZeroMode); with the")
print("   EP offsets that give m1 (u eps 0.0024, d 0.14) it is still <= 1e-6 at r = 1/32:")
for nm, s, eps in (("u", 1.14, 0.0024), ("d", 0.26, 0.14)):
    print(f"     {nm}: {leak(r0, -1+eps, s)[0]:.1e}")
# 3. a leakage deficit of the first row then comes through the heavier down modes:
Vus2, Vub2 = 0.2243**2, 0.00382**2          # comparison values only
cmid, cheavy = L[1]/r0**2, L[2]/r0**2
coef = Vus2*cmid + Vub2*cheavy
for dfc in (0.0009, 0.0016, 0.0023):
    print(f"3. deficit {dfc}: needs r = {np.sqrt(dfc/coef):.3f}")
# 3b. with the down protocol's fitted weight s_d = 0.26 the middle down mode leaks less:
cmid_d = leak(0.01, -1.0, 0.26)[1]/0.01**2
coef_d = Vus2*cmid_d
print(f"3b. with s_d = 0.26: middle down leakage {cmid_d:.3f} r^2; deficit 0.0016 needs r = {np.sqrt(0.0016/coef_d):.3f}")
print("4. candidate crossing programs (quarter-times) -> r = T/32 -> deficit:")
for nm, T in (("one quarter pulse", 1), ("one half-turn root event", 2), ("two half-turn root events (hop-like word)", 4),
              ("six reflections at a half turn each (register swap+triality)", 12)):
    r = T/32
    print(f"     {nm:58s} r = {r:.3f}  deficit ~ {coef*r*r:.1e}  heaviest-mode leakage {cheavy*r*r:.1e}")

# 5. the crossing as E8 reflections: carrier (a, 0) on wall 1 to (0, b) on wall 2.
import itertools
h = 0.5
Vc = [tuple(float(s_*(i == j)) for j in range(4)) for i in range(4) for s_ in (1, -1)]
Sc = [p for p in itertools.product((h, -h), repeat=4) if sum(x < 0 for x in p) % 2 == 0]
Cc = [p for p in itertools.product((h, -h), repeat=4) if sum(x < 0 for x in p) % 2 == 1]
cls = [Vc, Sc, Cc]
D4r = [r for r in {tuple(np.array(x) + np.array(y)) for x in Vc for y in Vc} if sum(z*z for z in r) == 2]
R = np.array([np.array(r + (0.,)*4) for r in D4r] + [np.array((0.,)*4 + r) for r in D4r]
             + [np.array(x + y) for c in range(3) for x in cls[c] for y in cls[c]])
def minlen(u, v, maxl=3):
    front = [u]
    for L_ in range(1, maxl + 1):
        new = []
        for w in front:
            for r in R:
                x = w - (w@r)*r
                if np.allclose(x, v): return L_
                new.append(x)
        front = list({tuple(np.round(x, 6)): x for x in new}.values())
    return None
u = np.array(cls[1][0] + (0.,)*4)
print("5. fewest E8 reflections taking a wall-1 carrier to a wall-2 carrier:",
      "same class", minlen(u, np.array((0.,)*4 + cls[1][0])), "| different classes (GenerationWalls)",
      minlen(u, np.array((0.,)*4 + cls[2][0])))
for T, nm in ((6, "3 reflections, certain (2 quarter-times each)"), (3, "3 reflections, one quarter-time each")):
    r = T/32
    print(f"   {nm}: r = {r:.4f}, deficit ~ {coef_d*r*r:.1e} (s_d = 0.26), heaviest leakage {cheavy*r*r:.1e}")
