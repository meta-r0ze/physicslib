#!/usr/bin/env python3
"""Check the massless-electron inclusive continuum muon spectrum.

The finite kernel F1 is Eq. (52) of Kühn and Mirkes, hep-ph/9301204.
Czarnecki and Melnikov, hep-ph/0112264, describe the Abelian mapping
to the muon neutrino-pair invariant. Here the color factor becomes 1,
so the rate density in z is F0(z) minus alpha/(2*pi) times F1(z).
The invariant uses the two neutrinos even in events with a real photon.

This starts from the published inclusive kernel. It checks the final
integration and normalization independently of the regulated diagrams.
"""

from fractions import Fraction
from math import log, log1p, pi
from typing import Callable

from scipy.integrate import quad
from scipy.special import spence


def tree_density(z: float) -> float:
    return 2 * (1 - z)**2 * (1 + 2 * z)


def inclusive_kernel(z: float) -> float:
    # scipy.special.spence(x) = Li_2(1 - x).
    return (
        tree_density(z) * (pi**2 + 2 * (spence(1 - z) - spence(z)))
        + 4 * z * (1 - z - 2 * z**2) * log(z)
        + 2 * (1 - z)**2 * (5 + 4 * z) * log1p(-z)
        - (1 - z) * (5 + 9 * z - 6 * z**2)
    )


def harmonic(n: int) -> Fraction:
    return sum((Fraction(1, k) for k in range(1, n + 1)), Fraction(0))


def polynomial_integral(
    coefficients: tuple[int, ...], moment: Callable[[int], Fraction]
) -> Fraction:
    return sum(
        (coefficient * moment(n + 1) for n, coefficient in enumerate(coefficients)),
        Fraction(0),
    )


def exact_integral() -> tuple[Fraction, Fraction]:
    # Moments of z^(m-1), with the dilogarithm moment obtained by parts:
    # Li_2(z) -> zeta(2)/m - H_m/m^2
    # log(z) -> -1/m^2, log(1-z) -> -H_m/m.
    def power_moment(m: int) -> Fraction:
        return Fraction(1, m)

    tree_normalization = polynomial_integral((2, 0, -6, 4), power_moment)
    # Reflect Li_2(1-z) to Li_2(z) in the integral.
    dilog_weight = (4, 0, -24, 16)  # 2 * (F0(z) - F0(1-z)).
    pi_squared_weight = tree_normalization + polynomial_integral(
        dilog_weight, power_moment
    ) / 6
    constant = (
        polynomial_integral(dilog_weight, lambda m: -harmonic(m) / m**2)
        + polynomial_integral((0, 4, -4, -8), lambda m: -Fraction(1, m**2))
        + polynomial_integral((10, -12, -6, 8), lambda m: -harmonic(m) / m)
        + polynomial_integral((-5, -4, 15, -6), power_moment)
    )
    return pi_squared_weight, constant


def main() -> None:
    pi_squared_weight, constant = exact_integral()
    if (pi_squared_weight, constant) != (1, Fraction(-25, 4)):
        raise ArithmeticError("Unexpected exact coefficients for the inclusive integral")
    tree, _ = quad(tree_density, 0, 1)
    inclusive, error = quad(inclusive_kernel, 0, 1, epsabs=1e-12, epsrel=1e-12)
    analytic = float(pi_squared_weight) * pi**2 + float(constant)
    if abs(tree - 1) > 1e-12 or abs(inclusive - analytic) > 1e-11 or error > 1e-11:
        raise ArithmeticError("Quadrature disagrees with the normalized exact integral")
    print(f"Integrated tree density: {tree:.15f}")
    print(f"Integrated F1: {inclusive:.15f} (quadrature error estimate {error:.2e})")
    print(f"Exact integral: {pi_squared_weight} * pi^2 + ({constant})")
    print(f"Rate coefficient in alpha/(2*pi): {-analytic:.15f}")


if __name__ == "__main__":
    main()
