#!/usr/bin/env python3
"""Run the ledger alpha_s from the Z down to the carrier cube's scale (comparison tool).

Inputs, all already in the library:
  * alpha_s(m_Z) = 0.1179952 (PMConstants strong coupling, read at the Z: ReadScale.colour_exact_read)
  * one-loop b0 = 11/3 N - 2/3 nf (PMAction.RunningCoefficients.b0, derived)
  * flavour thresholds at the E8 masses m_c, m_b (PMConstants.StrongRunning.mCharm/mBottom)
  * carrier cube scale 1/a = 317.5 MeV (PMHadrons.CubeScales: a = (4/m_p)/rho, rho = 1.354 sites)
Two-loop b1 = 102 - 38 nf/3 is the standard continuum value (not derived here); shown only to
test whether the one-loop number is stable.

Usage: python3 tools/cube_coupling_running.py
"""
import math
me = 0.51099895
mc = 4 * 1849 / (171 / 172 * 3) * me          # D Delta^2 / (overhead (sigma - chi))
mb = 1849 * (4 + 2 / 5) / (171 / 172) * me     # Delta^2 (D + chi/sigma) / overhead
mZ = 91187.6
a_inv = 317.5
aZ = 0.1179952


def b0(nf):
    return 11 - 2 * nf / 3


def b1(nf):
    return 102 - 38 * nf / 3


inv = 1 / aZ - b0(5) / (2 * math.pi) * math.log(mZ / mb) - b0(4) / (2 * math.pi) * math.log(mb / mc)
inv_cube = inv - b0(3) / (2 * math.pi) * math.log(mc / a_inv)
lam3 = mc * math.exp(-inv * 2 * math.pi / b0(3))
print('E8 thresholds: m_c %.1f MeV, m_b %.1f MeV' % (mc, mb))
print('one loop: alpha_s(m_c) %.3f, alpha_s(1/a) %.3f, Lambda_3 %.0f MeV, (1/a)/Lambda_3 %.2f'
      % (1 / inv, 1 / inv_cube, lam3, a_inv / lam3))


def run(a, m1, m2, nf, two_loop, steps=200000):
    t = math.log(m2 / m1) / steps
    for _ in range(steps):
        a += -(b0(nf) * a * a / (2 * math.pi) + two_loop * b1(nf) * a ** 3 / (8 * math.pi ** 2)) * t
        if a > 100:
            return math.inf
    return a


x = run(run(aZ, mZ, mb, 5, 1), mb, mc, 4, 1)
print('two loop: alpha_s(m_c) %.3f' % x)
for mu in (1000, 700, 500, 400, a_inv):
    print('  mu %6.1f MeV  alpha_s %s' % (mu, '%.3f' % run(x, mc, mu, 3, 1) if run(x, mc, mu, 3, 1) < 100 else 'pole above this scale'))
print('effective static coupling needed by the N-Delta splitting (tools/colour_fluctuation.py): 5.6')
