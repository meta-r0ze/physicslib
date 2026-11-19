# Closed-ring receiver test

## Encoding

`RingReceiver.tick` closes the certified two streams with
`finRotate N`. The two arrivals come from opposite neighbours.
The centre uses its retained requests for AND or OR. The probe uses
the same two clock slots and the clock advances through 43 phases.
`receiver_realisation` and `probe_realisation` give the agreement
with the existing local operations. `tick_bijective` gives the
inverse on the entire encoded state space.

The periodic identification is a finite model of the certified
root-line update. The last edge is a periodic boundary condition.
We do not infer a geometrically embedded ring of E8 sites from it.
The neighbourhood needs three distinct sites. A one-site ring
identifies them all, and `ring_neighbourhood` checks that two sites
coincide at the two incoming neighbours. We check three sites and
the next size, four. This is an explicit computational bound.

## Stationary orbits

The requests are constant on each orbit. `ports_iterate` gives
a permutation of the two port fields for that request pattern.
`port_step_source` reduces it to a permutation on the individual
slots. Lean checks all switch patterns on three and four sites
(`slot_period_three`, `slot_period_four`), with common port periods
12 and 24. The probe returns after two clock periods. Consequently
the clocked state from phase zero returns by tick 516 or 1032
respectively (`ring_return_three`, `ring_return_four`). These are
common bounds. A particular orbit can close sooner.

`enumerateOrbits` deduplicates the sets of states reached from
phase-zero seeds. `orbit_enumeration_covers` proves coverage.
`arrivalFrequency` and `requestFrequency` give stationary
frequencies at any receiver. `portPopulation` gives the time
average for either port and any supplied population of each label.
The Boolean labels are distinct port values. In the flag example
both label values can be occupied. The Boolean zero does not
designate the physical packet vacancy.

For the numerical enumeration, `python3 tools/ring_receiver_check.py`
factors out the clock and independent probes. Its `--traffic`
output gives every request and port orbit with multiplicity,
joint arrival counts and port-pair counts at every node. Divide the
counts by the listed port period. This retains the probe-degenerate
orbits. Indeed, for a port orbit of length `L`, every 43rd tick
visits the same port orbit because 43 is coprime to 12 and 24.
`probe_one_period` toggles a probe exactly on a mixed request.
The simultaneous probe map therefore has order `D = 2` if any
request is mixed and order one otherwise. The phase-zero joint
orbit length is `lcm(L,D)`. There are `2^N L` phase-zero seeds
in this group. Division by the joint length gives the number of
distinct full orbits. All orbits in that group have the same port
and arrival counts. The script checks that orbit lengths sum to
the full state count `43 × 32^N`.

| Sites | AND orbits | OR orbits |
| --- | ---: | ---: |
| 3 | 7,104 | 12,416 |
| 4 | 214,048 | 359,968 |
