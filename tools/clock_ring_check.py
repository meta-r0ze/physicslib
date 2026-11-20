"""Clock closure of the encoded root line (exploration; no data).

The clock's states are the discriminant group of the E8 clock plane
Z cu + Z cv (PMSubstrate.ClockPlane: Gram [[2,1],[1,22]], form x^2+xy+11y^2,
clock_glue: w -> w1 - 2 w2 mod 43). A lattice point z reads the clock as
phase(z) = (<z,cu> - 2<z,cv>) mod 43.

Checks:
1. how many of the 240 E8 roots change the clock reading, and by how much;
2. the roots that advance the reading by exactly +1 (one tick per root event)
   and their split by projection onto the clock plane;
3. that the -1 roots are the negatives of the +1 roots (two streams);
4. the colour-reference overlap used in the composition note.
Since 43 is prime, a walk whose every step changes the reading by +1 or -1
lives on Z/43: the receiver's periodic identification is the clock cycle.
"""
import collections
import numpy as np

G = np.array([[2,0,-1,0,0,0,0,0],[0,2,0,-1,0,0,0,0],[-1,0,2,-1,0,0,0,0],
              [0,-1,-1,2,-1,0,0,0],[0,0,0,-1,2,-1,0,0],[0,0,0,0,-1,2,-1,0],
              [0,0,0,0,0,-1,2,-1],[0,0,0,0,0,0,-1,2]])
cu = np.array([1,0,0,0,0,0,0,0]); cv = np.array([0,-2,-1,1,-1,0,0,0])
ip = lambda a, b: int(a @ G @ b)
phase = lambda z: (ip(z, cu) - 2 * ip(z, cv)) % 43

simple = [np.eye(8, dtype=int)[i] for i in range(8)]
roots = {tuple(s) for s in simple}; frontier = list(roots)
while frontier:
    new = []
    for r in frontier:
        r = np.array(r)
        for s in simple:
            t = tuple(r - ip(r, s) * s)
            if t not in roots:
                roots.add(t); new.append(t)
    frontier = new
roots = [np.array(r) for r in roots]
assert len(roots) == 240 and all(ip(r, r) == 2 for r in roots)

c = collections.Counter(phase(r) for r in roots)
print("roots:", len(roots))
print("clock-silent roots (phase 0):", c[0],
      "of which orthogonal to the clock plane:",
      sum(1 for r in roots if ip(r, cu) == 0 and ip(r, cv) == 0))
print("roots that change the reading:", 240 - c[0])
plus = [r for r in roots if phase(r) == 1]
minus = [r for r in roots if phase(r) == 42]
print("one-tick roots: +1:", len(plus), " -1:", len(minus))
print("-1 roots are the negatives of the +1 roots:",
      sorted(map(tuple, minus)) == sorted(tuple(-r) for r in plus))
print("+1 roots by (<r,cu>, <r,cv>):",
      dict(collections.Counter((ip(r, cu), ip(r, cv)) for r in plus)))

# Colour reference: unit colour-symmetric state vs a colour axis state.
ov = 1 / np.sqrt(3)
print("colour-axis overlap with the symmetric colour state: 1/sqrt3 =", ov)
print("interference mismatch (1 - overlap)/2 =", (1 - ov) / 2,
      " comparison angle x = arccos(1/sqrt3) =", np.degrees(np.arccos(ov)), "deg")
