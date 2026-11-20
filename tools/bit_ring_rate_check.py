#!/usr/bin/env python3
"""Exploration only: one firing site on the bit ring.

No data.  The packet starts live at x0; the request field fires at one site s.
The printed counts are receiver flags over T=43 ticks for n=3..8 and n=43.
This is a finite observation, not a Lean theorem and not a mass.
"""
from itertools import product


def rot(n, x):
    return (x + 1) % n


def invrot(n, x):
    return (x - 1) % n


def step(n, q, ports):
    out = []
    for x in range(n):
        p = (ports[invrot(n, x)][0], ports[rot(n, x)][1])
        out.append((p[1], p[0]) if q[x] else p)
    return out


def flag(n, q, ports, x):
    a = (ports[invrot(n, x)][0], ports[rot(n, x)][1])
    return int(q[x] and a[0] != a[1])


def total(n, s, x0, ticks=43):
    q = [False] * n
    q[s] = True
    ports = [(False, False)] * n
    ports[x0] = (True, False)
    out = 0
    for _ in range(ticks):
        out += sum(flag(n, q, ports, x) for x in range(n))
        ports = step(n, q, ports)
    return out


def main():
    print("one firing site, T=43, counts by x0 for firing site s=0")
    for n in range(3, 9):
        print(f"n={n}: {[total(n, 0, x0) for x0 in range(n)]}")
    vals = {total(43, s, x0) for s in range(43) for x0 in range(43)}
    print(f"n=43: distinct counts over all firing sites and x0 = {sorted(vals)}")


if __name__ == "__main__":
    main()
