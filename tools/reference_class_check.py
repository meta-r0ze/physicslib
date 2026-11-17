#!/usr/bin/env python3
"""Which reference class vectors are stationary when native class exchanges are kept or suppressed
(PMAction REVIEW, "Node-restoring amplitude": the reference occupies one class).

On the reference wall every native exchange between distinct classes is the same scalar on the
reference's sector (CarrierAdmittance.uniform_hop). A reference spread over classes with weights u
(class 0 = v) stays a zero mode iff X u = 0, X = lambda * adjacency of the exchanges kept.
Enumerate the kept-exchange sets and their stationary references."""
import itertools, sympy as sp
edges = [(0, 1), (0, 2), (1, 2)]
names = "vsc"
for r in range(4):
    for E in itertools.combinations(edges, r):
        A = sp.zeros(3, 3)
        for i, j in E:
            A[i, j] = A[j, i] = 1
        ns = A.nullspace()
        kept = ",".join(f"{names[i]}<->{names[j]}" for i, j in E) or "none"
        refs = [list(v.T) for v in ns]
        print(f"kept {{{kept}}}: stationary references span {refs}")
