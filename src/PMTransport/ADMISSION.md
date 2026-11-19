# Reachability of native transport traces

## Starting state

| Certificate | What it fixes | What the physical initial state still needs |
| --- | --- | --- |
| `CarrierVacuumSector.range_iff_odd`, `identification` | The accessible carrier representation is the antipodal-odd sector of each class, with the stated Hamiltonian readout. | The occupied sites, class and amplitudes. The sector contains coherent states. |
| `RegisterVacuum.isometry`, `evolution_readout`, `IndependentRegisters.occupied_encode` | The occupied two-bank encoding and its evolution for supplied inputs and parameters. | The physical occupation sector and contents of each bank, including the request register. |
| `NativeReferenceBackground.stationary_iff`, `referenceField_fixed`, `minimum_in_family_iff` | For the specified connected finite update, the live and record copy of each active mode share one common value throughout the connected orbit. This applies in particular at a node and its neighbours. Other fields are free. A stationary witness in the accessible family minimizes the specified positive excess price. | The neighbourhood update and accessible occupation family. The common value is free even in the stationary family. In the linear field model zero and nonzero common fields are stationary. |
| `SharedReference.reserved_single`, `shared`, `ReferenceEconomy.economy_selects_lepton` | Maximal payload with a nonempty reservation gives one cell for both refreshes. The allocation model selects the lepton type under colour preservation. | The occupied state arriving at a writer and the map from the reserved cell to its timed ports. |
| `OddReferenceSource.rest_stationary`, `rest_modes_distinct`, `rest_population`, `odd_seed_train_restores` | In each class and on each wall there are two distinct exhibited unit-population rest seeds. The loaded first-wall vector seed gives a ready reference on the open route when supplied before each visit. | Which modes the background actually occupies, and which ready values feed the route. The finite index `Fin 3 × Bool × Bool` lists the coordinate seed witnesses. There is no completeness or accessibility certificate for this list as an initial-state family. |

The fixed-field and supply theorems describe different parts of the
problem. On an exactly homogeneous live and record pair, the supplied
finite update preserves the same contents. A packet reaching the writer
needs a specified excitation or incoming stream on that background.
`OpenHandoff.acceptance_iff_supply` constrains readiness on one line.
`any_incoming_trace` allows independently specified traffic on the other.
The family of physically accessible initial microstates has no finite
encoding in the present results. There is no basis for counting it as the
coordinate witnesses, a product of independent ports, or the uniform
packet inventory.

**Background occupancy and boundary supply.** Specify the accessible
occupied configurations, including excitations and controller states, and
the incoming boundary contents for the chosen clock horizon. To count
priors, give a finite enumeration or a certified finite quotient with
its fibre sizes.

## Update and horizon

Use the node and sites −1 and +1 for the first open visit, along the
primitive root of `OpenHandoff.address_step`. A visit is a routing step.
A theorem assigning these visits to particular substrate ticks is still
needed.

| Operation | Certified update | Admission still needed |
| --- | --- | --- |
| Root trial at phases 0 and 1 | `ClockedRootTrials.ticks_zero_one`, `ticks_one_two`, `pair_endpoint`. The requests are initial state fields. Each true request applies the same root. | The accessible controller states and the attachment of the clocked carrier probe to actual ports. |
| Root trial at phases 2–42 | `iterate_controls`, `quiet_trial_tick`, `trial_period_endpoint`. In this trial the requests and carrier persist while the clock advances. | The other operations that may use these slots. |
| Spatial shift, exchange or bypass | `TwoSiteHandoff.native_step_observed`, `step_trace`, `export_trace` give the destinations for a supplied exchange bit. In the open exchange, `receiver_trace` puts the incoming ready reference in the live port and the previous live arrival in the record. | The clock-conditioned spatial shift, branch bit and downstream port attachment. |
| Additional register controls | `RegisterControl.extend_encode`, `occupation_conserved`, `phase_unitary` apply to a supplied control and preserve the occupation count. | The joint per-tick operation and how it sets or reuses controls and records. The trial and handoff interfaces take different states. No theorem joins them. |

For visit `k` the open receiver reads initial ports at `−k` and `+k`.
Through `N` executed visits its arrivals therefore depend only on the
corresponding initial upstream ports. `export_trace` gives the record
at each displaced address for that horizon. However,
`neighbours_do_not_determine_second_visit` gives two completions of
the same three-site start with the same ready reference at every visit
and different second records. A three-site calculation is sufficient
for the first visit only, unless later arrivals are fixed by a boundary
law. A closed finite ring is a different update.

One 43-tick period suffices to check the isolated trial pair from phase
zero, including its quiet suffix. It gives no whole-wire upper bound.
The conditional serial lower bounds in [CLOCK.md](CLOCK.md#periods-per-route)
are 60 and 152 ticks for the two direct words and 36 and 88 before
additional work for the restoring words. A schedule across more than
one period needs the admitted intervening operations and supply
at each additional visit. The current clock and route results provide
no finite upper bound on this schedule.

**Joint clocked controller.** Give the reversible successor of the
occupied wire, reference and record state at each phase, including the
guard that binds the request and delivered port to each operation.
The certified updates above fix those transitions whose controls and
inputs are already specified.

## Exhaustive trial histories and conditional counts

For a fixed supplied initial lattice carrier `z`, write `Rz` for its
reflection. The trial state keeps both request bits at every tick.
There is no export or consumption operation in this trial. After the
second request the lattice component stays at its endpoint through
tick 43. The table enumerates every encoded trace from phase zero.

| Retained pair | Guard fires at | After tick 1 | After tick 2 through 43 | One state per pair | One state per shared request |
| --- | --- | --- | --- | ---: | ---: |
| false, false | Neither phase | z | z | 1 | 1 |
| false, true | Phase 1 | z | Rz | 1 | 0 |
| true, false | Phase 0 | Rz | Rz | 1 | 0 |
| true, true | Both phases | Rz | z | 1 | 1 |

The first two tick equations and `trial_period_endpoint` give the
carrier columns. `all_pairs_history_count` and
`shared_request_history_count` check the finite counts. Even when
`Rz = z`, the retained requests distinguish these histories in the
trial state. If the initial controller microstates differ in other
fields, the count of a history is the size of its initial request
fibre (`history_count_pos_iff`). This disallows inferring equal
physical counts from reversibility or from the two clock slots. The
two columns are conditional enumerations of specified initial control
encodings.

For the open handoff, `receiver_trace` and `export_trace` describe
the live, ready and displaced values for every supplied arrival and
every visit within the horizon. There is no enumeration of joint
wire traces from the persisting background until the two gaps above
are filled. In particular, combining the trial table with each
possible handoff branch by a Cartesian product would require a proof
that the input controllers and ports admit those combinations.

## Consequences for the wire

| Question | Result of the reachability check |
| --- | --- |
| Writer population | With a common ready reference, `any_incoming_trace` realizes any supplied live arrival sequence in the open model. The restored live port contains the reference, and the displaced record port contains that sequence. The node law is compatible with different traffic and does not identify the writer's input port. `VacancyProjection.occupied_fixed_iff` excludes the sterile basis slot from occupied payloads. It leaves idle bookings and active probes open. None of the three uniform policies is forced. |
| Heavy branch | `HeavyFlipControl.direct_iff` gives address zero. `no_root_only_direct_address` excludes a guard that reads only the untagged glued root. `ElectricCompanionBank.guarded_companion_transport` gives the candidate with the prepared tag and electric record. The joint controller must supply and retain the tag on the direct wall and fire the guarded crossing. The two reference polarities remain candidates. |
| Lightest-offset branch | `ChargedInsertion.joint_selector` has support only at address two on a matching charged static label. `matched_flags_zero` gives zero flags on the two matched comparisons. It leaves their control and the offset firing open. The joint controller must retain their plus records and bind them and the static vector test to the pulse. |
| Trial priors | The same update gives four histories with one state per pair and two histories with one state per shared request. Physical equality requires the accessible finite controller background and its request fibres. |
| Physical schedule | The trial slots are fixed in the stated experiment. The wire's operation order, overlaps and times of repeat visits need a joint controller and boundary supply. |

**Record reference undetermined.** For two admitted writers with a
common booked population, let `M_L` and `M_C` be the booked colourless
and coloured input masses. The output flag difference is
`G = M_L − M_C` by `WireReferenceCost.booked_population_difference`.
If both writers also pay a separate balanced reset per independent
bit, `booked_balanced_reset_difference` gives the total signed
colour-minus-lepton cost `U + (3/2)(M_L − M_C)`. Here `U` is the
difference in remaining paid work, in the same units. Its sign
selects colour when negative, ties at zero and selects lepton when
positive, provided both schedules are admitted.

The [three reset-inclusive thresholds](../PMElementaryParticles/SCHEDULE.md#record-reference-remains-undetermined)
are conditional cases of this account. The decisive missing inputs
are the booked traffic and polarity traces from **Background occupancy
and boundary supply** and the **Joint clocked controller**, followed
by the signed remainder under the [Registration tariff](PREMISES.md#registration-tariff).
For this decision only, under a common population it suffices to give
the signed sector mass difference and enough unmatched paid work to
bound the total on one side of zero. If the two admitted polarities
use different traffic, compute the two weighted charges separately.

## No external controller

### Finite encoding

The certified streaming step sends one input from each neighbour
along the chosen root line. Its local output therefore needs the
centre and the two adjacent sites. The bypass reads both neighbours,
so a radius-zero encoding loses its arrivals. At the centre the
trial probe reads the retained request pair and the shared phase.
It applies the on-site root in phases 0 or 1 as specified by
`ClockedRootTrials`. The phase advances in `Fin Δ`.

`LocalController` uses two distinguishable port values, the two
retained request bits and the two points on a moving root orbit.
This is the smallest alphabet for testing order, all four requests,
and both outcomes of a reflection. A rule gives one exchange or
bypass decision per phase, request pair and arriving port pair.
`radius_one`, `receiver_realisation` and `probe_realises_trial`
check the local operations against their certified forms. The same
table applies at every site. The three-site stencil is a finite
encoding of one update, and the global rule acts on the open line.
One stream shift per encoded tick is part of this model. The physical
shift duration on the substrate clock remains open.

This encoding restricts the guard to the arrivals and the local
retained requests. In particular it keeps the probe and transport
registers independent. Locality also allows other guards on the same
neighbourhood. The library supplies no finite quotient of the full
coherent wire that preserves its writer, branch records and costs.
An enumeration here tests whether the stated constraints force a
unique rule even within this restricted family.

### Reversible rule family

At each phase and for each retained request pair, there are 16
Boolean tables. The unequal arrivals `01` and `10` must have the
same guard decision. Different decisions send both inputs to the
same output. On `00` and `11`, either decision gives the same port
values and the table still records which operation ran.

`LocalController.reversible_iff_rows` lifts this test to a global
bijection on the open line with the shared clock. It uses the inverse
stream shift, the involutive local switch and the inverse phase
advance. `reversible_rows_count` checks all 16 rows in the kernel.
`enumerated_rule_iff` enumerates precisely the reversible tables
by independent choices of these rows. There are eight choices at
each of four requests and 43 phases, hence `8^(4 × 43)` tables
(`enumerated_rule_count`). Requiring the tagged receiver trace below
fixes the two diagonal request rows in each phase. Each of the
two mixed request rows still has eight choices. This counts literal guard tables and
requires no quotient or symmetry assumption.

### Reachability per rule

| Input or question | Consequence of the enumerated rule |
| --- | --- |
| Uniform occupied field with equal live and record ports | Both values stay equal at every site, for every table and every tick (`uniform_ports_iterate`). This is the uniform port projection of the certified stationary reference fields. It supplies the same value on each stream but does not choose which physical reference occupies them. |
| Trial probe on any supplied moving root orbit | `read_trial_iterate` reduces every projected trace to `ClockedRootTrials.tick`. All tables preserve the four initial request fibres. The counts are `(1,1,1,1)` for one state per pair or `(1,0,0,1)` for one per shared request in the order above. The accessible controller states determine which counts apply. |
| Tagged open receiver | If the centre carries the double request and the rest of the line carries the idle pair, a table that exchanges and bypasses on those tags respectively realizes the open-line trace exactly (`tagged_open_iterate`). At visit `k` it reads the ready reference at `+k`, retains the live arrival at `−k`, and exports earlier records as in `receiver_trace` and `export_trace`. The initial tags and contents specify this conditional trace. The rule does not allocate them. |
| Mixed requests and unequal arrivals | `two_open_compatible_rules` gives two reversible tables agreeing on the entire tagged receiver trace. One exchanges on two true bits, the other on either true bit. `mixed_requests_different_destinations` shows the different outputs for the same input with exactly one set request. |
| Writer population and heavy and light branches | Neither the port alphabet nor the trial bit is a packet or companion record. The trace supplies the ordered port values, with no identification of the writer's port, vacancy guard, electric polarity, or retained heavy and light guards. The existing heavy and light candidate support remains as stated above. |

A three-site stencil applies at each tick. To compute `N` open
visits from initial data at a single centre requires the upstream
ports through `±N` or a law supplying them. A single period tests
the trial or the local rule at each phase. The direct and restoring
serial lower bounds still govern any proposed longer physical wire.

### Persistence selection

`traceExchangeToll` prices every table with the sum of its weighted
exchange output flags over a supplied finite set of visits. An exchange
compares its arriving values with flag `‖L − R‖²/2`
(`TwoSiteHandoff.exchange_flag`, `exchange_flag_realisation`).
Bypass contributes zero to this receiver account. The visit weights
come from the paid sampling law. `NetCost.expected_count_linear`
justifies adding expected registrations. The resulting amplitude
with total Toll `T` is `exp(−T/2)` (`TollAmplitude.wireAmplitude`).

**Outcome (b), tie in the certified flag account.** On the supplied
uniform reference fields, every table keeps the ports equal and all
its exchange flags vanish (`uniform_trace_exchange_toll`). The
two-site hop flag also vanishes on the corresponding uniform inputs
(`TwoSiteHandoff.hop_flag`). The root probe trace and its local-change
action are common for a fixed initial probe family. With those accounts
and a common baseline, `uniform_flag_persistence_tie` applies
`PersistenceSelection.within_family_iff_cheapest`. Every table ties.
The two example rules also agree on the tagged open receiver's
branch at every visit, even with nonuniform arrivals.

On the uniform trace a strict preference is equivalent to a strict
difference in remaining paid work (`uniform_remaining_cost_iff`).
The exact guard difference between the two witnesses is whether a
single retained request triggers exchange. To distinguish their port
traces, the accessible family must include a mixed request with two
unequal arrivals. To distinguish their physical costs, supply the
booked frequency and tariff for any visits where they differ, or a
signed difference in control and other remaining paid work on the
same traces. Reversibility and the listed primitive operations do
not give those inputs.

The tie applies to the stated account and family. The full wire
still needs its occupied state family, controller and paid work. The record reference remains
undetermined. The reset-inclusive bounds `3/4`, `27/32` and `9/10`
from the [writer schedule](../PMElementaryParticles/SCHEDULE.md#record-reference-remains-undetermined)
still require the actual booked population, admitted writer polarities,
separate balanced resets and the signed remaining price.

### Candidate postulate

The occupied state at a receiver determines which retained signal
triggers each operation. The signal stays available to reverse the
operation or leaves in a specified record. State how the incoming
ports supply the signal and which values fire exchange, bypass,
writing and the later pulses.

For example, one possible receiver law would exchange exactly when
both local request bits are set, retaining the bits for reversal.
The rule that exchanges when either bit is set is another possibility.
They agree on the tagged receiver. The library adopts neither law.
