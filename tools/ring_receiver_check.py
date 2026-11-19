"""Exact finite enumeration for PMTransport.RingReceiver, with orbit multiplicity."""

import argparse
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from itertools import product
from math import gcd, lcm, log

PERIOD = 43  # PMSubstrate.E8Values.Delta_eq
PORT_PERIOD = {3: 12, 4: 24, 5: 120}  # RingReceiver.slot_period_three/four/five


def pair_at(ports: int, site: int) -> int:
    return (ports >> (2 * site)) & 3


def arrivals(ports: int, n: int, site: int) -> int:
    west_live = pair_at(ports, (site - 1) % n) & 1
    east_record = pair_at(ports, (site + 1) % n) & 2
    return west_live | east_record


def step(ports: int, switches: tuple[bool, ...]) -> int:
    result = 0
    n = len(switches)
    for site, exchange in enumerate(switches):
        pair = arrivals(ports, n, site)
        if exchange:
            pair = (pair >> 1) | ((pair & 1) << 1)
        result |= pair << (site * 2)
    return result


@dataclass(frozen=True)
class PortCycle:
    first: int
    length: int
    arrivals: tuple[tuple[int, ...], ...]
    ports: tuple[tuple[int, ...], ...]


@cache
def port_cycles(switches: tuple[bool, ...]) -> tuple[PortCycle, ...]:
    n = len(switches)
    seen = set()
    cycles = []
    for first in range(1 << (2 * n)):
        if first in seen:
            continue
        ports = first
        incoming = [[0] * 4 for _ in range(n)]
        occupied = [[0] * 4 for _ in range(n)]
        length = 0
        while ports not in seen:
            seen.add(ports)
            length += 1
            for site in range(n):
                incoming[site][arrivals(ports, n, site)] += 1
                occupied[site][pair_at(ports, site)] += 1
            ports = step(ports, switches)
        assert ports == first and PORT_PERIOD[n] % length == 0
        cycles.append(PortCycle(first, length, tuple(map(tuple, incoming)),
                                tuple(map(tuple, occupied))))
    return tuple(cycles)


def enumerate_traffic(n: int, either: bool):
    for requests in product(range(4), repeat=n):
        switches = tuple(bool(q) if either else q == 3 for q in requests)
        # Each mixed request toggles its own probe once per clock period.
        # Thus the joint probe update has order two if any request is mixed.
        probe_order = 2 if any(q in (1, 2) for q in requests) else 1
        for cycle in port_cycles(switches):
            # Sampling the port orbit every 43 ticks permutes its starting phases.
            assert gcd(PERIOD, cycle.length) == 1
            block_count = lcm(cycle.length, probe_order)
            count, remainder = divmod((1 << n) * cycle.length, block_count)
            assert remainder == 0
            yield requests, switches, cycle, PERIOD * block_count, count


def tolls(switches: tuple[bool, ...], cycle: PortCycle):
    # Pair encodings 1 and 2 have unequal values. Certify the unit flag
    # for these encodings in RingReceiver.receiver_flag_eq.
    return tuple(Fraction(row[1] + row[2], cycle.length) if exchange else Fraction(0)
                 for exchange, row in zip(switches, cycle.arrivals))


def cost_histograms(n: int, either: bool, show_traffic: bool):
    histograms = {
        (scope, traffic, prior): Counter()
        for scope in ("site", "ring")
        for traffic in ("all", "positive", "exchange", "requested")
        for prior in ("orbit", "state")
    }
    periods = Counter()
    for requests, switches, cycle, period, count in enumerate_traffic(n, either):
        periods[period] += count
        cost = tolls(switches, cycle)
        if show_traffic:
            print(n, "OR" if either else "AND", requests, cycle, period, count)
        for scope, toll, exchanges, requested in (
            ("site", cost[0], switches[0], bool(requests[0])),
            ("ring", sum(cost), any(switches), any(requests)),
        ):
            for traffic, keep in (
                ("all", True), ("positive", toll > 0), ("exchange", exchanges),
                ("requested", requested),
            ):
                if keep:
                    histograms[scope, traffic, "orbit"][toll] += count
                    histograms[scope, traffic, "state"][toll] += count * period
    assert sum(period * count for period, count in periods.items()) == PERIOD * 32**n
    print(n, "OR" if either else "AND", "orbits", sum(periods.values()),
          "periods", dict(sorted(periods.items())))
    return histograms


def comparison_polynomials(and_hist, or_hist, scale: int):
    # x = exp(-beta/scale). Clearing positive denominators gives
    # polynomials whose positive sign favours AND.
    assert all((scale * t).denominator == 1 for t in and_hist.keys() | or_hist.keys())
    and_terms = {int(scale * t): w for t, w in and_hist.items()}
    or_terms = {int(scale * t): w for t, w in or_hist.items()}
    mean_gap = Counter()
    for i, a in and_terms.items():
        for j, b in or_terms.items():
            mean_gap[i + j] += (j - i) * a * b

    and_count = sum(and_terms.values())
    or_count = sum(or_terms.values())
    conditional_gap = Counter({i: w * or_count for i, w in and_terms.items()})
    conditional_gap.subtract({j: w * and_count for j, w in or_terms.items()})
    pooled_gap = Counter(and_terms)
    pooled_gap.subtract(or_terms)
    return mean_gap, conditional_gap, pooled_gap


def descartes_signs(terms):
    # Remove x^k, which is positive on the open unit interval. Then set
    # x = y/(1+y) and multiply by (1+y)^degree. The nonzero coefficient
    # sign changes bound the number of roots in 0 < x < 1.
    lowest, highest = min(terms), max(terms)
    coeffs = [0] * (highest - lowest + 1)
    for exponent, weight in terms.items():
        power = highest - exponent
        binomial = 1
        for j in range(power + 1):
            coeffs[exponent - lowest + j] += weight * binomial
            binomial = binomial * (power - j) // (j + 1)
    signs = []
    for coefficient in coeffs:
        if coefficient:
            sign = 1 if coefficient > 0 else -1
            if not signs or signs[-1] != sign:
                signs.append(sign)
    return signs


def sign_at(terms, x: Fraction):
    # Evaluate the numerator of the polynomial with sparse integer Horner.
    powers = sorted(terms, reverse=True)
    degree = previous = powers[0]
    value = terms[degree]
    for exponent in powers[1:]:
        value = (value * x.numerator ** (previous - exponent)
                 + terms[exponent] * x.denominator ** (degree - exponent))
        previous = exponent
    return (value > 0) - (value < 0)


def isolate_root(terms, left, right, left_sign):
    # Endpoint signs can be one-sided at 0 or 1.
    for _ in range(33):
        middle = (left + right) / 2
        middle_sign = sign_at(terms, middle)
        if middle_sign == 0:
            return middle, middle
        if middle_sign == left_sign:
            left = middle
        else:
            right = middle
    return left, right


def comparison_profile(coefficients, scale: int):
    terms = {i: c for i, c in coefficients.items() if c}
    if not terms:
        return "tie"
    signs = descartes_signs(terms)
    name = {1: "AND", -1: "OR"}
    if len(signs) == 1:
        return f"{name[signs[0]]} for all beta > 0"

    # Each witnessed change needs a root. Once every permitted
    # change is witnessed, Descartes excludes any other root.
    points = [(Fraction(0), signs[0])]
    if len(signs) == 3:
        middle = next(Fraction(k, 64) for k in range(1, 64)
                      if sign_at(terms, Fraction(k, 64)) == signs[1])
        points.append((middle, signs[1]))
    assert len(points) == len(signs) - 1
    points.append((Fraction(1), signs[-1]))
    brackets = [isolate_root(terms, left, right, sign)
                for (left, sign), (right, _) in zip(points, points[1:])]
    winners = " -> ".join(name[sign] for sign in reversed(signs))
    thresholds = ", ".join(f"{-scale * log(float((lo + hi) / 2)):.6f}"
                           for lo, hi in reversed(brackets))
    exact = ", ".join(f"[{lo}, {hi}]" for lo, hi in reversed(brackets))
    return f"{winners} as beta increases, switches near {thresholds}, x brackets {exact}"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--traffic", action="store_true",
                        help="show each request and port cycle with its full orbit multiplicity")
    parser.add_argument("--histograms", action="store_true",
                        help="show the exact prior mass at each Toll for both rules")
    args = parser.parse_args()
    for n, scale in PORT_PERIOD.items():
        and_hist = cost_histograms(n, False, args.traffic)
        or_hist = cost_histograms(n, True, args.traffic)
        for label, a in and_hist.items():
            b = or_hist[label]
            print(n, *label, f"minima {min(a)}, {min(b)}")
            if args.histograms:
                for name, hist in (("AND", a), ("OR", b)):
                    print(" ", name, " ".join(f"{t}:{mass}" for t, mass in sorted(hist.items())))
            polys = comparison_polynomials(a, b, scale)
            for score, poly in zip(("mean Toll", "equal-rule survival", "pooled rule share"), polys):
                print(" ", score, comparison_profile(poly, scale))
        # Change only the prior at one common, exactly specified hazard.
        for prior, expected in (("orbit", -1), ("state", 1)):
            key = "ring", "all", prior
            if n == 5:
                mean, _, _ = comparison_polynomials(and_hist[key], or_hist[key], scale)
                assert sign_at(mean, Fraction(2, 3)) == expected
            if n == 3:
                _, _, pooled = comparison_polynomials(and_hist[key], or_hist[key], scale)
                assert sign_at(pooled, Fraction(49, 50)) == expected


if __name__ == "__main__":
    main()
