"""Exact finite enumeration for PMTransport.RingReceiver, with orbit multiplicity."""

import argparse
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from itertools import product
from math import gcd, lcm

PERIOD = 43  # PMSubstrate.E8Values.Delta_eq
PORT_PERIOD = {3: 12, 4: 24}  # RingReceiver.slot_period_three/four


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


def exp_negative_bounds(x: Fraction):
    # The tail after term 50 is alternating with strictly decreasing
    # magnitude for the checked range. Use consecutive partial sums.
    assert 0 <= x <= 4
    term = upper = Fraction(1)
    for k in range(1, 51):
        term *= -x / k
        upper += term
    return upper - term * x / 51, upper


def gibbs_bounds(histogram: Counter):
    denominator_low = denominator_high = Fraction(0)
    numerator_low = numerator_high = Fraction(0)
    for cost, count in histogram.items():
        low, high = exp_negative_bounds(cost)
        denominator_low += count * low
        denominator_high += count * high
        numerator_low += count * cost * low
        numerator_high += count * cost * high
    return numerator_low / denominator_high, numerator_high / denominator_low


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--traffic", action="store_true",
                        help="show each request and port cycle with its full orbit multiplicity")
    args = parser.parse_args()
    for n in PORT_PERIOD:
        means = []
        for either in (False, True):
            periods = Counter()
            site_costs = Counter()
            ring_costs = Counter()
            for requests, switches, cycle, period, count in enumerate_traffic(n, either):
                periods[period] += count
                cost = tolls(switches, cycle)
                site_costs[cost[0]] += count
                ring_costs[sum(cost)] += count
                if args.traffic:
                    print(n, "OR" if either else "AND", requests, cycle, period, count)
            assert sum(period * count for period, count in periods.items()) == PERIOD * 32**n
            print(n, "OR" if either else "AND", "orbits", sum(periods.values()),
                  "periods", dict(sorted(periods.items())))
            assert site_costs[0] and ring_costs[0]
            bounds = []
            for name, histogram in (("site 0", site_costs), ("ring sum", ring_costs)):
                low, high = gibbs_bounds(histogram)
                print(name, "minimum", min(histogram), "Gibbs mean at beta=1",
                      f"{float((low + high) / 2):.9f}")
                print("cost counts", " ".join(f"{c}:{m}" for c, m in sorted(histogram.items())))
                bounds.append((low, high))
            means.append(bounds)
        for (_, and_high), (or_low, _) in zip(*means):
            assert and_high < or_low


if __name__ == "__main__":
    main()
