#!/usr/bin/env python3
"""Exploration only: checkerboard/Dirac spectrum for the bit-ring hypothesis.

No data.  Two amplitudes per site (live, record).  A tick shifts live one way
and record the other way, then a coin rotates by theta at every firing site.
Empty firing has no coin (gapless); full firing has the coin at every site.
The script prints the quasienergy gap and a small-k fit to
E^2 = a^2 sin^2(k) + m^2.  It is not a certified EP result.

The Lean coherent encounter and full-firing tick are
`PhaseToRecord.encounter_unitary`, `CoherentRing.ringTick_unitary`, and the
plane-wave period `Dispersion.planeWave_exp_period`; the block action, `M(k)`,
and eigenvalue proof are not completed.  The mass reading is a hypothesis.
"""
import numpy as np


def spectrum(n, firing, theta):
    k = 2 * np.pi * np.arange(n) / n
    phases = []
    c, s = np.cos(theta / 2), -1j * np.sin(theta / 2)
    for kk in k:
        S = np.diag([np.exp(-1j * kk), np.exp(1j * kk)])
        C = np.array([[c, s], [s, c]]) if firing == "full" else np.eye(2)
        U = S @ C
        phases.append(np.sort(np.angle(np.linalg.eigvals(U))))
    return np.array(phases), k


def main():
    n = 256
    for theta in [0.1, 0.2, 0.4, 0.8]:
        empty, k = spectrum(n, "empty", theta)
        full, _ = spectrum(n, "full", theta)
        gap_empty = np.min(empty[:, 1] - empty[:, 0])
        gap_full = np.min(full[:, 1] - full[:, 0])
        mask = (k > 0.01) & (k < 0.3)
        A = np.vstack([np.sin(k[mask]) ** 2, np.ones(mask.sum())]).T
        a2, m2 = np.linalg.lstsq(A, full[mask, 0] ** 2, rcond=None)[0]
        exact = np.arccos(np.cos(theta / 2) * np.cos(k))
        err = np.max(np.abs(np.abs(full[:, 0]) - exact))
        print(f"theta={theta:.2f} gap_empty={gap_empty:.3e} "
              f"gap_full={gap_full:.6f} m_exact={gap_full/2:.6f} "
              f"m2_fit={m2:.3e} a2_fit={a2:.3e} cosE_err={err:.2e}")


if __name__ == "__main__":
    main()
