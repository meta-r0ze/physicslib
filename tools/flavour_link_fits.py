#!/usr/bin/env python3
"""Numerical checks for the CKM on the generation-class incidence network (PMFlavor).

Not part of the axiom-checked tree. Records the scans behind the "Real legs are excluded in either
reading" paragraph of src/PMFlavor/OVERVIEW.md.

Data:
  CKM: PDG 2024 Wolfenstein fit, lambda = 0.22501(68), A = 0.826(+16/-15),
       rhobar = 0.1591(94), etabar = 0.3523(+73/-71).
  Quark masses at M_Z (GeV): u 1.23e-3, c 0.620, t 168.3, d 2.67e-3, s 0.0531, b 2.839
       (Xing-Zhang-Zhou running-mass tables); only ratios enter.

Model:
  A sector link is a Kron-reduced incidence network with complex legs (LinkFlux): a magnetic
  Laplacian on the generation triangle, off-diagonal moduli x, y, z, one flux F, diagonal = sum
  of the incident moduli.

Checks:
  1. transfer_bound: real K, V = expm(-iK): |V_ub| >= |V_us||V_cb|/2 (PDG ratio 0.40).
  2. transfer_flux: masses generation-diagonal, CKM = expm(-iK) or Cayley(K); fit the four
     rephasing invariants. Reports the flux (form-dependent, 43-49 deg) and |K13|.
  3. eigen_fit: both sectors are magnetic-Laplacian mass links, masses delta0^2/sigma (seesaw)
     or the exact one-flavour (sqrt(s^2 + 4 d^2) - s)/2; CKM = U_u^H U_d. Best chi2 ~ 1040,
     dominated by m_s/m_d.

Run: python3 tools/flavour_link_fits.py   (about a minute)
"""
import numpy as np
from scipy.linalg import expm
from scipy.optimize import least_squares

CENT = (0.22501, 0.826, 0.1591, 0.3523)
ERR = (0.00068, 0.0155, 0.0094, 0.0072)
MU, MC, MT = 1.23e-3, 0.620, 168.3
MD, MS, MB = 2.67e-3, 0.0531, 2.839


def ckm(lam, A, rb, eb):
    s12, s23 = lam, A * lam**2
    z = (rb + 1j * eb) * np.sqrt(1 - A**2 * lam**4) / (
        np.sqrt(1 - lam**2) * (1 - A**2 * lam**4 * (rb + 1j * eb)))
    s13e = A * lam**3 * z
    s13, e = abs(s13e), np.exp(1j * np.angle(s13e))
    c12, c23, c13 = (np.sqrt(1 - s**2) for s in (s12, s23, s13))
    return np.array([
        [c12 * c13, s12 * c13, s13 / e],
        [-s12 * c23 - c12 * s23 * s13 * e, c12 * c23 - s12 * s23 * s13 * e, s23 * c13],
        [s12 * s23 - c12 * c23 * s13 * e, -c12 * s23 - s12 * c23 * s13 * e, c23 * c13]])


def invariants(V):
    """|V_us|, |V_cb|, |V_ub|, 1e3 J (rephasing invariant)."""
    J = np.imag(V[0, 1] * V[1, 2] * np.conj(V[0, 2]) * np.conj(V[1, 1]))
    return np.array([abs(V[0, 1]), abs(V[1, 2]), abs(V[0, 2]), 1e3 * J])


def magnetic(x, y, z, F):
    return np.array([[x + z, -x, -z * np.exp(-1j * F)],
                     [-x, x + y, -y],
                     [-z * np.exp(1j * F), -y, y + z]])


def offdiag(x, y, z, F):
    return np.array([[0, -x, -z * np.exp(-1j * F)], [-x, 0, -y], [-z * np.exp(1j * F), -y, 0]])


def cayley(K):
    return np.linalg.solve(np.eye(3) + 0.5j * K, np.eye(3) - 0.5j * K)


def deg(F):
    return (np.degrees(F) + 180) % 360 - 180


def transfer_bound():
    V = ckm(*CENT)
    ratio = abs(V[0, 2]) / (abs(V[0, 1]) * abs(V[1, 2]))
    # real K: the smallest |V_ub| at the PDG |V_us|, |V_cb| over K13
    best = None
    for g13 in np.linspace(-0.01, 0.01, 2001):
        def f(q):
            Vt = expm(-1j * np.array([[q[0] + g13, -q[0], -g13], [-q[0], q[0] + q[1], -q[1]],
                                      [-g13, -q[1], q[1] + g13]]))
            return [abs(Vt[0, 1]) - abs(V[0, 1]), abs(Vt[1, 2]) - abs(V[1, 2])]
        q = least_squares(f, [0.227, 0.042]).x
        Vt = expm(-1j * np.array([[q[0] + g13, -q[0], -g13], [-q[0], q[0] + q[1], -q[1]],
                                  [-g13, -q[1], q[1] + g13]]))
        if best is None or abs(Vt[0, 2]) < best:
            best = abs(Vt[0, 2])
    print(f"1. PDG |V_ub|/(|V_us||V_cb|) = {ratio:.3f}; real-K transfer minimum |V_ub| = {best:.5f}"
          f" vs PDG {abs(V[0, 2]):.5f}")


def fit_transfer(gen, Kf, target):
    best = None
    for F0 in np.linspace(-3, 3, 13):
        r = least_squares(lambda q: invariants(gen(Kf(*q))) - target, [0.23, 0.042, 0.004, F0])
        if r.cost < 1e-20 and (best is None or r.x[2] > 0):
            best = r
    x, y, z, F = best.x
    if z < 0:
        z, F = -z, F + np.pi
    return x, y, z, deg(F)


def transfer_flux():
    t = invariants(ckm(*CENT))
    for gname, gen in (("exp(-iK)", lambda K: expm(-1j * K)), ("Cayley", cayley)):
        for kname, Kf in (("magnetic", magnetic), ("off-diag", offdiag)):
            x, y, z, F = fit_transfer(gen, Kf, t)
            print(f"2. {gname:8s} {kname:8s} |K12|={x:.5f} |K23|={y:.5f} |K13|={z:.5f} flux={F:.2f}")
    rng = np.random.default_rng(1)
    Fs = []
    for _ in range(200):
        p = tuple(c + e * rng.standard_normal() for c, e in zip(CENT, ERR))
        Fs.append(fit_transfer(lambda K: expm(-1j * K), magnetic, invariants(ckm(*p)))[3])
    print(f"   exp/magnetic flux, PDG errors: {np.mean(Fs):.1f} +- {np.std(Fs):.1f} deg;"
          f" VubSeriesPath 1/(2a^-1+pi) = {1 / (2 * 137.035999 + np.pi):.5f}")


def sector(x, y, z, F):
    w, U = np.linalg.eigh(magnetic(x, y, z, F))
    return w[::-1], U[:, ::-1]          # light .. heavy (mass ~ 1/sigma)


def eigen_fit(exact):
    target = invariants(ckm(*CENT))
    sig = np.array([0.0007, 0.0008, 0.0002, 0.0015])

    def resid(q):
        wu, Uu = sector(1, np.exp(q[0]), np.exp(q[1]), q[2])
        wd, Ud = sector(1, np.exp(q[3]), np.exp(q[4]), q[5])
        if exact:
            du, dd = np.exp(q[6]), np.exp(q[7])
            mu = (np.sqrt(wu**2 + 4 * du**2) - wu) / 2
            md = (np.sqrt(wd**2 + 4 * dd**2) - wd) / 2
        else:
            mu, md = 1 / wu, 1 / wd
        r = [np.log(mu[1] / mu[0] / (MC / MU)), np.log(mu[2] / mu[1] / (MT / MC)),
             np.log(md[1] / md[0] / (MS / MD)), np.log(md[2] / md[1] / (MB / MS))]
        r = np.array(r) / 0.05
        return np.r_[r, (invariants(Uu.conj().T @ Ud) - target) / sig]

    n = 8 if exact else 6
    lb = [-25, -25, -4 * np.pi, -25, -25, -4 * np.pi, -25, -25][:n]
    ub = [8, 8, 4 * np.pi, 8, 8, 4 * np.pi, 8, 8][:n]
    rng = np.random.default_rng(7)
    best = None
    for _ in range(400):
        q0 = np.r_[rng.uniform(-12, 4, 2), rng.uniform(-np.pi, np.pi),
                   rng.uniform(-12, 4, 2), rng.uniform(-np.pi, np.pi), rng.uniform(-12, 4, 2)][:n]
        try:
            with np.errstate(all="ignore"):
                r = least_squares(resid, q0, bounds=(lb, ub))
        except (np.linalg.LinAlgError, ValueError):
            continue
        if np.isfinite(r.cost) and (best is None or r.cost < best.cost):
            best = r
    label = "exact one-flavour, delta0 free" if exact else "seesaw delta0^2/sigma"
    print(f"3. eigenvector reading ({label}): best chi2 = {2 * best.cost:.0f};"
          f" residuals (4 mass ratios at 5%, 4 CKM in sigma) {np.round(resid(best.x), 2)}")


if __name__ == "__main__":
    transfer_bound()
    transfer_flux()
    eigen_fit(exact=False)
    eigen_fit(exact=True)
