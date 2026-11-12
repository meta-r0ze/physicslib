#!/usr/bin/env python3
"""The proton's Coulomb pull on the emitted electron: lattice cube vs continuum (comparison tool).

Lepton cube (PMHadrons.CubeScales): 3^3 Dirichlet Laplacian in units of m_e, hop = m_e, so
a_e = 1/(sqrt2 m_e) and the potential is -kappa alpha G(., centre) with kappa = 4 pi sqrt2
(`lepton_hop`). The rate goes as the electron density at the proton, so the Coulomb factor is
|psi(centre)|^2 with the potential over |psi(centre)|^2 without it.

Checks:
  1. the 3^3 cube, and larger n^3 cubes at the same spacing;
  2. refining the spacing inside the same physical box (continuum-box limit);
  3. the non-relativistic Sommerfeld factor pi alpha / v at the lattice mode's own velocity;
  4. the relativistic Fermi factor 2 pi eta/(1 - exp(-2 pi eta)), eta = alpha E/p, averaged over the
     continuum spectrum p E (E0 - E)^2 with the E8 endpoint E0 = m_n - m_p = 2.531 m_e.

Usage: python3 tools/lepton_coulomb.py
"""
import itertools
import math
import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as sla

alpha = 1 / 137.036
kappa = 4 * math.pi * math.sqrt(2)


def lap(n):
    I = sp.identity(n)
    T = sp.diags([2 * np.ones(n), -np.ones(n - 1), -np.ones(n - 1)], [0, 1, -1])
    return (sp.kron(sp.kron(T, I), I) + sp.kron(sp.kron(I, T), I) + sp.kron(sp.kron(I, I), T)).tocsc()


def coulomb(n, h=1.0):
    """Density gain at the centre on an n^3 interior grid with spacing h (units of a_e)."""
    L = lap(n)
    c = (n // 2) * (n * n + n + 1)
    e = np.zeros(n ** 3)
    e[c] = 1
    G = sla.spsolve(L, e)
    H0 = L / h ** 2
    H = H0 - sp.diags(kappa * alpha * G / h)
    w0, v0 = sla.eigsh(H0, k=1, sigma=0)
    _, v1 = sla.eigsh(H, k=1, sigma=0)
    return v1[c, 0] ** 2 / v0[c, 0] ** 2 - 1, w0[0]


print('1. lowest mode, spacing a_e, n^3 cube:')
for n in (3, 5, 7, 9, 15):
    g, E = coulomb(n)
    print('   n %2d  T %.3f m_e  Coulomb gain %.4f' % (n, E, g))
print('2. same 3-site box, finer spacing (h = 1/m):')
for m in (1, 2, 4, 8):
    g, E = coulomb(4 * m - 1, 1 / m)
    print('   m %d  T %.3f m_e  Coulomb gain %.4f' % (m, E, g))
T3 = coulomb(3)[1]
v = math.sqrt(2 * T3)
print('3. 3^3 mode: T = %.3f m_e, non-relativistic v = %.2f c; pi alpha / v = %.4f' % (T3, v, math.pi * alpha / v))


def fermi(E):
    p = math.sqrt(E * E - 1)
    x = 2 * math.pi * alpha * E / p
    return x / (1 - math.exp(-x))


E0 = 2.531
num = den = 0.0
N = 20000
for i in range(1, N):
    E = 1 + (E0 - 1) * i / N
    p = math.sqrt(E * E - 1)
    wgt = p * E * (E0 - E) ** 2
    num += wgt * fermi(E)
    den += wgt
Erel = 1 + T3
print('4. relativistic Fermi factor: at the 3^3 mode read relativistically (T = %.3f, beta = %.2f) %.4f;'
      % (T3, math.sqrt(1 - 1 / Erel ** 2), fermi(Erel)))
print('   averaged over the continuum spectrum to E0 = %.3f m_e: %.4f (supplied factor 1.0322)' % (E0, num / den))
