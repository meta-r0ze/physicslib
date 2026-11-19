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
