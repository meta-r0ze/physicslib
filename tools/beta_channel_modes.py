#!/usr/bin/env python3
"""Which modes the emitted electron has: confined cube vs unbounded lattice vs continuum (comparison tool).

The E8 spectral template (NeutronPrediction, BetaCalibration) is
    rate = (G_F^2/3) * f_B,   f_B = sum_{lambda <= Q} e^{-lambda} / sum_all e^{-lambda}
over the Dirichlet modes of an n^3 lepton cube. Persistence reading tested here: the emitted electron
is not a resource of any persistent volume (it leaves through the Toll boundary), so nothing confines
it, and its modes are those of the unbounded lattice at its own spacing (n -> infinity).

1. f_B as the cube grows, for the neutron and for tritium (two cutoff conventions);
2. the continuum route, the same phase space as the muon (PMElementaryParticles.MuonRate, PolarMeasure):
   rate = G_F^2 |V_ud|^2 (1 + 3 g_A^2) R f / (2 pi^3),  f = int F(E) p E (E0 - E)^2 dE,
   with E8 inputs: G_F m_e^2 = 3.0457e-12, |V_ud| = 0.974495, R = 1.021179 (ShortDistanceRunning),
   E0 = m_n - m_p = 2.530989 m_e, alpha; g_A = 5/4 (E8) or 1.2754 (measured, comparison).
   F is the Fermi factor 2 pi eta/(1 - exp(-2 pi eta)), eta = alpha E/p.

Usage: python3 tools/beta_channel_modes.py
"""
import math
import numpy as np

alpha = 1 / 137.036
GF = 3.0457e-12
Vud = 0.974495
R = 1.021179
E0 = 1838.68366205 - 1836.15267344
t_me = 1.28808867e-21   # hbar/(m_e c^2) in s


def f_boltzmann(n, Q):
    k = np.arange(1, n + 1)
    e1 = 2 - 2 * np.cos(np.pi * k / (n + 1))
    lam = (e1[:, None, None] + e1[None, :, None] + e1[None, None, :]).ravel()
    w = np.exp(-lam)
    return w[lam <= Q].sum() / w.sum()


print('1. Boltzmann open fraction f_B on n^3 (lifetime scales as 1/f_B):')
for Q, name in ((E0, 'neutron, cutoff m_n - m_p'), (1.0364, 'tritium, cutoff Q + m_e'),
                (0.0364, 'tritium, cutoff Q')):
    print('   %-26s' % name, '  '.join('%d: %.3g' % (n, f_boltzmann(n, Q)) for n in (3, 5, 9, 31, 121)))
print('   neutron lifetime: 948.7 s on 3^3 -> %.0f s on the unbounded lattice'
      % (948.7 * f_boltzmann(3, E0) / f_boltzmann(121, E0)))


def fermi(E):
    p = math.sqrt(E * E - 1)
    x = 2 * math.pi * alpha * E / p
    return x / (1 - math.exp(-x))


def f_phase(E0, coulomb, N=200000):
    s = 0.0
    for i in range(1, N):
        E = 1 + (E0 - 1) * i / N
        p = math.sqrt(E * E - 1)
        s += (fermi(E) if coulomb else 1) * p * E * (E0 - E) ** 2
    return s * (E0 - 1) / N


f0, fC = f_phase(E0, False), f_phase(E0, True)
print('2. continuum route: f = %.4f without Coulomb, %.4f with (ratio %.4f)' % (f0, fC, fC / f0))
for gA in (1.25, 1.2754):
    for f, lab in ((f0, 'no Coulomb'), (fC, 'Coulomb')):
        G = GF ** 2 * Vud ** 2 * (1 + 3 * gA ** 2) * f * R / (2 * math.pi ** 3)
        print('   g_A %.4f  %-10s  tau = %.1f s  (%+.1f%% vs 878.4 s)' % (gA, lab, t_me / G, 100 * (t_me / G / 878.4 - 1)))
fT = f_phase(1 + 0.0364, False, 20000)
print('   phase-space ratio tritium/neutron: %.2e (Boltzmann template on the unbounded lattice: %.2e)'
      % (fT / f0, f_boltzmann(121, 0.0364) / f_boltzmann(121, E0)))
