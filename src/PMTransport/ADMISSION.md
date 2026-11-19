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
