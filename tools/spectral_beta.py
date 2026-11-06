#!/usr/bin/env python3
"""Finite E8 spectral beta weights (comparison tool, not a Lean theorem)."""
import math


def eigenvalue(n, a, b, c):
    return (6
            - 2 * math.cos(math.pi * a / (n + 1))
            - 2 * math.cos(math.pi * b / (n + 1))
            - 2 * math.cos(math.pi * c / (n + 1)))


def fraction(n, cutoff):
    weights = []
    for a in range(1, n + 1):
        for b in range(1, n + 1):
            for c in range(1, n + 1):
                weights.append(math.exp(-eigenvalue(n, a, b, c)))
    total = sum(weights)
    opened = sum(w for w, lam in zip(
        weights,
        (eigenvalue(n, a, b, c)
         for a in range(1, n + 1)
         for b in range(1, n + 1)
         for c in range(1, n + 1)),
    ) if lam <= cutoff)
    return opened / total


if __name__ == "__main__":
    for n in (3, 4, 5, 6, 8, 10):
        print(f"n={n}")
        for cutoff in (2.0, 4.0, 6.0, 10.0):
            print(f"  E={cutoff:4.1f}  weight fraction={fraction(n, cutoff):.6f}")
