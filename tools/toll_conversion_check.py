#!/usr/bin/env python3
"""Toll-to-amplitude conversion check for the heavy-label weight (external, numerical).

`ProtocolToll.hyperchargeFlag_schedule_bound` excludes the ladder s_e < s_d < s_u with
s_u >= 2 s_d for a common *affine* map from a static hypercharge Toll to the wire amplitude.
This script asks what the same static flags allow under the two multiplicative conversions the
library already uses elsewhere:

  survival   s = exp(-lam T / 2), T = floor + sum_i w_i f_i   (DecayLaw: per-tick cost -> exp)
  retained   s = prod_i sqrt(P_i), P_i the retained port      (VacancyPreparation: port products)

Static flag at step t: f = sin^2(t * tag / 6), tags e -6, d -2, u 4, vacancy 0
(`hyperchargeFlag_eq_cos`). With x = t/3: f_e = sin^2 3x, f_d = sin^2 x, f_u = sin^2 2x.

Prints:
1. no single step gives T_e > T_d > T_u; a nonnegative schedule does (LP), so under the
   survival conversion the static flags reach the recorded order;
2. retained minus port: s_u/s_d = 2|cos x| per step, and < sqrt(2) on every step with s_d > s_e,
   so s_u/s_d ~ 4.4 needs at least five such steps; retained plus port with s_d > s_e gives
   s_u/s_d < 1.
PMAction.TollAmplitude now derives the survival form with lam = 1 (Paper I's linear cost and the
rare-registration limit); the retained-port product is its single-step lower bound. The schedule
is still open. No value here is derived.
"""
import numpy as np
from scipy.optimize import linprog

x = np.linspace(0, np.pi, 40001)[1:-1]
fe, fd, fu = np.sin(3 * x) ** 2, np.sin(x) ** 2, np.sin(2 * x) ** 2
a, b = fe - fd, fd - fu  # T_e - T_d and T_d - T_u per unit weight

print("1. survival conversion")
print("   single step with T_e > T_d > T_u:", bool(np.any((a > 1e-12) & (b > 1e-12))))
r = linprog(np.ones_like(x), A_eq=np.vstack([a, b]), b_eq=[1.0, 1.0], bounds=(0, None))
print(f"   schedule with T_e - T_d = T_d - T_u = 1: status {r.status}, total weight {r.fun:.4f}")
for t_over_pi in (0.5, 1.5):
    xx = t_over_pi * np.pi / 3
    print(f"   step t = {t_over_pi}pi: f_e, f_d, f_u = "
          f"{np.sin(3*xx)**2:.4f}, {np.sin(xx)**2:.4f}, {np.sin(2*xx)**2:.4f}")
# recorded heavy weights (protocol_readout_scan.py, k = alpha/2): s_d/s_e 2.67-3.18, s_u/s_d 4.25-4.53
print("   needed (lam = 1): T_e - T_d = 2 ln(s_d/s_e) in [1.96, 2.31], T_d - T_u = 2 ln(s_u/s_d) in [2.89, 3.02]")

print("2. retained-port conversion")
minus_d_over_e = fd > fe
ratio_ud = 2 * np.abs(np.cos(x))
print(f"   minus port, steps with s_d > s_e: max s_u/s_d = {ratio_ud[minus_d_over_e].max():.6f}"
      f" (sqrt 2 = {np.sqrt(2):.6f}); vacancy amplitude 0 on every step")
need = 4.25
n = int(np.ceil(np.log(need) / np.log(np.sqrt(2))))
print(f"   s_u/s_d >= {need} then needs at least {n} such steps")
c = np.cos(x) ** 2
plus_d_over_e = c > c * (4 * c - 3) ** 2
ratio_plus = np.abs(np.cos(2 * x)) / np.abs(np.cos(x))
print(f"   plus port, steps with s_d > s_e: max s_u/s_d = {ratio_plus[plus_d_over_e].max():.6f}")
