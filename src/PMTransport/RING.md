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
coincide at the two incoming neighbours. The checks cover three,
four and five sites. `ring_five_neighbourhood` checks the last size.

## Stationary orbits

The requests are constant on each orbit. `ports_iterate` gives
a permutation of the two port fields for that request pattern.
`port_step_source` reduces it to a permutation on the individual
slots. Lean checks all switch patterns on three, four and five sites
(`slot_period_three`, `slot_period_four`, `slot_period_five`), with
common port periods 12, 24 and 120. The probe returns after two clock
periods. From phase zero the clocked state returns by tick 516,
1032 or 5160 (`ring_return_three`, `ring_return_four`, `ring_return_five`). These are
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
counts by the listed port period. In the printed pair order, live
label 1 occurs in bins 1 and 3, and record label 1 in bins 2 and 3.
This retains the probe-degenerate orbits. For a port orbit of
length `L`, every 43rd tick visits the same port orbit because 43
is coprime to each tested port period.
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
| 5 | 4,126,528 | 10,569,280 |

## Pricing and selection

`receiver_flag_eq` evaluates the certified receiver comparator on
two orthogonal unit port values. An unequal pair contributes one
to the exchange account. Equal pairs and bypass contribute zero.
`orbitToll` takes the uniform orbit average of these receiver flags.
It counts expected registrations per common tick. It can sum over
any supplied receiver set. This account charges the receiver flags.
It supplies no additional probe, controller or preparation tariff.

`minimum_orbit_toll` gives zero for both rules. Its witness has the
same occupied value in the two streams, even with mixed requests.
Every orbit has nonnegative Toll. The proof applies at any ring
size with a complete orbit enumeration and to any receiver set.
`both_rules_attain_best_survival` applies
`PersistenceSelection.within_family_iff_cheapest` to the joint family
of rules and orbits. Both rules attain the maximum survival.

For comparison, `gibbsOrbitMean` gives one prior count to each
distinct orbit. For an orbit-cost histogram `H(T)`, the mean is
`Σ H(T) T exp(−βT) / Σ H(T) exp(−βT)`. This is the original
three- and four-site comparison at `β = 1`, the survival exponent
for `wireAmplitude T = exp(−T/2)`. The table gives rounded means.
A common tick provides the same cost horizon across orbit lengths.

| Sites | Minimum, either rule | Gibbs mean at site 0, AND | OR | Gibbs mean over ring sum, AND | OR |
| --- | ---: | ---: | ---: | ---: | ---: |
| 3 | 0 | 0.087222214 | 0.289593246 | 0.243445155 | 0.858742518 |
| 4 | 0 | 0.071325547 | 0.293279325 | 0.233922525 | 1.130260829 |

## What Paper I selects

`PersistenceSelection.within_family_iff_cheapest` ranks individual
candidates with supplied actions in a supplied family. If a candidate
is a tagged orbit, the cheapest orbit attains the best individual
survival. `Selection.selection_principle` gives the long-time
statement for that ensemble. With positive supplied priors and a
common hazard, histories with a cost rate above the minimum lose
all survivor share. It does not choose a rule when each has an
orbit at the same minimum rate.

`Selection.survivor` weights each history by its prior times
`exp(−β S)`, with `S` the accumulated action at a common horizon.
If a rule is a class of histories, `survivor_mass_of_subset`
gives its share as the sum of those weights divided by the common
normalization. This is a marginal survival share. It is not the
mean cost of the histories conditional on surviving. If each
rule first has a separately supplied prior, normalize the within-rule
prior before calculating its marginal. If one runs a rule through
successive states, a theorem must supply its accumulated action.
`LawSelection.law_selection` also takes the law's rate as an input.

`Gibbs.probability_eq_survivor` identifies Gibbs with survivor weights
at equal priors. It does not say whether initial states, distinct
orbits, or rules get equal prior weight. The library gives no rule-level
selection by the conditional mean Toll. It supplies no canonical
rule ensemble, accessible prior or action for a single whole rule.

## Robustness across all positive hazards

The checked scope is the encoded ring and its receiver flags. We use
one count per distinct orbit or one count per state, the latter
multiplying the orbit count by the full clocked length. We check
the sum over all receivers and the flag account at site zero.

| Filter | Orbits retained in the scored scope |
| --- | --- |
| All | Every orbit. |
| Positive | Orbits with strictly positive Toll. This drops every zero-flag orbit. |
| Exchange | Orbits with an exchange at a scored site. Equal-arrival exchanges remain. |
| Requested | Orbits with at least one set request at a scored site. |

The lowest Toll ties in every row under both priors. It is zero
except under the positive filter. There the site minima are
`1/4`, `1/6`, `1/8` and the ring minima are `1/3`, `1/4`, `1/5`
for three, four and five sites, respectively. Those positive
minima are from the orbit enumeration.

For each rule, let `H(T)` be the prior mass at Toll `T`. The pooled
survivor share ranks `Z = Σ H(T) exp(−βT)` across the rules. The
equal-rule survival column divides each `Z` by that rule's prior
mass before comparison. The mean column ranks the mean Toll
conditional on survival, with lower Toll preferred.

The calculation covers all `β > 0`. Let `D` be the common port
period and put `x = exp(−β/D)`. Every `D T` is integral, so the
partition functions are integer polynomials in `x`. Clearing the
positive denominators gives an integer polynomial for each gap.
After removing its lowest power of `x`, substitute
`x = y/(1+y)` and clear powers of `1+y`. Descartes' rule bounds
the number of zeros on `0 < x < 1` by the coefficient sign changes.
Exact rational signs witness every possible crossing here.
`python3 tools/ring_receiver_check.py --histograms` gives the
histograms, sign profiles and exact rational root brackets in `x`.
The Lean certificates establish the finite return bounds and
receiver flags. The histograms and polynomial sign certificates
are computed in the script.

In the tables A is AND and O is OR. A single letter applies at
every positive hazard. Arrows show the order as the hazard increases.
Numbers in parentheses are rounded transition hazards, with equality
at each exact root.

### Ring sum

| Sites | Filter | Mean, orbit | Mean, state | Equal rule, orbit | Equal rule, state | Pooled, orbit | Pooled, state |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 3 | all | A | A | A | A | O→A (0.778316) | A |
| 3 | positive | A | A | A | A | O→A (3.178076) | O→A (1.589662) |
| 3 | exchange | A→O (4.818138) | A→O (4.941899) | A | A | O→A→O (4.053227, 5.859058) | O→A (1.383889) |
| 3 | requested | A | A | A | A | O→A (0.778316) | A |
| 4 | all | A | A | A | A | O→A (0.467771) | A |
| 4 | positive | A | A | A | A | O→A (1.794628) | O→A (0.580356) |
| 4 | exchange | A→O (4.467440) | A→O (4.364804) | A | A | O→A (1.670942) | O→A (0.535790) |
| 4 | requested | A | A | A | A | O→A (0.467771) | A |
| 5 | all | A→O (21.117831) | A | A | A | O→A (0.787921) | A |
| 5 | positive | A | A | A | A | O→A (1.305991) | O→A (0.285713) |
| 5 | exchange | A→O (5.364041) | A→O (6.481760) | A | A | O→A (1.271464) | O→A (0.267258) |
| 5 | requested | A→O (33.440875) | A | A | A | O→A (0.787921) | A |

### Site zero

| Sites | Filter | Mean, orbit | Mean, state | Equal rule, orbit | Equal rule, state | Pooled, orbit | Pooled, state |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 3 | all | A | A | A | A | O→A (3.381504) | A |
| 3 | positive | A→O (16.644081) | A→O (11.661167) | A | A→O (39.185444) | O | O |
| 3 | exchange | A→O (0.224178) | O | A→O (0.448991) | O | O | O |
| 3 | requested | A | A | A | A | O→A (2.529575) | A |
| 4 | all | A | A | A | A | O→A (2.525542) | A |
| 4 | positive | A | A | A | A | O | O |
| 4 | exchange | A→O (0.371838) | O | A→O (0.747694) | O | O | O |
| 4 | requested | A | A | A | A | O→A (2.119217) | A |
| 5 | all | A→O (36.111243) | A→O (69.804823) | A | A | O | A |
| 5 | positive | A | A | A | A | O→A (36.590662) | O→A (24.666282) |
| 5 | exchange | A→O (0.000888) | O | A→O (0.001776) | O | O | O |
| 5 | requested | A→O (47.895991) | A | A | A | O→A (5.680439) | A |

With five sites and all orbits, at `x = 2/3` the ring mean favours
OR per orbit and AND per state. The common hazard is
`120 log(3/2)`. With three sites and all orbits, the pooled survivor
share likewise favours OR per orbit and AND per state at
`x = 49/50`, or `β = 12 log(50/49)`. Both reversals use exact
rational signs. The chosen prior changes the answer even with
the rule, scope, idle filter and hazard held fixed.


## Boundary erasure

This ring retains both streams and supplies no exported bit.
`BoundaryErasure.ring_boundary_step` and `ring_cycle_erasure`
give zero erased bits per period and zero erasure Toll per tick
for AND and OR at every ring size. This tie holds for any prior.
`ring_live_depends_on_record` shows why erasing a circulating
record would change the retained update. A new ring with disposal
needs a separate export port and a certificate identifying which
information has finished its internal use.

The tables above count comparison flags with the stated prior.
They remain results of that account. The
[boundary stopping point](PREMISES.md#stopping-point) leaves the
erasure-merged prior unevaluated.
