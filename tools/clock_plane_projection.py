"""Clock-plane projections of the generation cosets (exploration; no data).

For every aligned placement (tools/generation_clock_signature.py), project each
local root (clock reading 0 or +-1) onto the clock plane, p(r) = (<r,cu>, <r,cv>),
and compare with the receiver ring step (a spacetime-D4 root reading +1).

Result, the same in all 10 aligned placements:
  conjugate spinor (4,4,8), library g=1: ring steps equal the spacetime ring step;
      its 8 silent roots project to (0,0) (internal, in the clock's A4).
  spinor (4,4,0), library g=2: ring steps differ from the spacetime step by cu;
      no silent roots.
  vector (7,7,2), library g=0: ring steps differ from the spacetime step by cu;
      its 2 silent roots are +-cu (transverse in the clock plane).
So silent roots are of two kinds: internal (g=1) or transverse (g=0).
"""
import os, io, contextlib, collections, itertools
import numpy as np

here = os.path.dirname(os.path.abspath(__file__))
src = open(os.path.join(here, "generation_clock_signature.py")).read()
ns = {}
with contextlib.redirect_stdout(io.StringIO()):
    exec(src[:src.index("seen=collections.Counter()")], ns)
ip, ph, cu, cv, roots, pl = (ns[k] for k in ("ip", "ph", "cu", "cv", "roots", "pl"))
proj = lambda r: (ip(r, cu), ip(r, cv))

def cosets(D4):
    Dint = [r for r in roots if all(ip(r, x) == 0 for x in D4)]
    rest = [r for r in roots if r not in D4 and r not in Dint]
    bas = []
    for sys_ in (D4, Dint):
        for comb in itertools.combinations(sys_, 4):
            M = np.array([[ip(x, y) for y in comb] for x in comb])
            if round(abs(np.linalg.det(M))) == 4:
                bas += list(comb); break
    inv = np.linalg.inv(np.array(bas, dtype=float).T)
    classes = []
    for r in rest:
        for cl in classes:
            c = inv @ (np.array(r) - np.array(cl[0]))
            if np.allclose(c, np.round(c)): cl.append(r); break
        else:
            classes.append([r])
    return classes

summary = collections.Counter()
for D3, D4 in pl:
    D4 = list(D4)
    ring = {proj(r) for r in D4 if ph(r) == 1}
    assert len(ring) == 1
    (step,) = ring
    rows = []
    for cl in cosets(D4):
        sig = tuple(sum(ph(r) == k for r in cl) for k in (1, -1, 0))
        plus = {proj(r) for r in cl if ph(r) == 1}
        sil = {proj(r) for r in cl if ph(r) == 0}
        aligned = plus == {step}
        offset = {(p[0] - step[0], p[1] - step[1]) for p in plus}
        kind = "none" if not sil else ("internal" if sil == {(0, 0)} else
               ("transverse +-cu" if sil == {(2, 1), (-2, -1)} else str(sil)))
        rows.append((sig, "aligned" if aligned else f"offset {sorted(offset)}", kind))
    summary[tuple(sorted(rows))] += 1

for rows, n in summary.items():
    print(f"{n} placements:")
    for sig, ring_rel, kind in rows:
        print(f"  coset {sig}: ring steps {ring_rel}; silent roots {kind}")
