# Receiver rule and downstream quantities

This inventory separates fixed inputs and conditional formulae from
observations of a receiver trace. The latter can see the rule even
when the former have no receiver argument.

| Surface | What it supplies | What the receiver rule could change |
| --- | --- | --- |
| `Values`, clock | `Delta`, `shortSerialTicks`, `longSerialTicks`, their minima, `shortSerialR`, `longSerialR`, and `equal_normalization_rate`. | The period, serial budgets and normalized ratios have fixed arguments. A physical choice of word, overlap or timing is a separate trace input. |
| `Values`, thresholds | `outputFlagThreshold`, `balancedResetThreshold` and their case values. | These are fixed functions of sampling and flag accounting. The selection that uses them also needs the actual booked costs. |
| `Interface.Handoff` | The two-site step and destinations, repair and return, flags, half-pulse, left outflow, conductance, and independent through paths. | Which branch fires controls the live and record destinations and whether the exchange comparison runs. The coefficient `α`, the stipulated current law, and the independent-path formula are fixed at the same premises. |
| `Interface.Record` | Open receiver and export traces, their population and supply, odd reference preparation, retained restoration, orthogonality and the register-control and pulse contract. | A different port order can change which live state is restored and which value is retained or routed on. The tagged open route agrees in both rules. The preparation and storage requirements apply to their specified inputs and operations. |
| `Interface.Cost` | Expected counts, diagonal flags, `scheduleToll`, survival and amplitude, selection and refresh. | Costs can change if the booked encounters differ. The cost and amplitude maps and the minimum theorem remain the same for the same arguments. |
| `Interface.Clock` | Period, quarter and half pulses, word lengths, slot histories, priors conditional on preparation, and clock calibration. | At a common start the retained requests, probe and clock advance independently of the guard. A distribution over different starts and an admitted physical schedule are further inputs. |
| `Interface.Route` | Wall orientation, glue address, stationary reference-class test, direct and restoring paths, two equal legs and the crossing identities. | The predicates and effective series weight `α/2` at the stated assumptions are fixed. A live packet's actual route through a mixed-request receiver can differ. |
| EP tier and mass ledger | `TierLedger.tiersFor`, `QuarkMasses`, `LeptonMasses`. Their inputs are the declared tier lists, substrate counts including `Δ`, `D`, `sigma`, `chi`, and the supplied overhead, charge and conversion constants. | There is no receiver-rule argument in the tier lists or mass formulae. These values give no identification of a selected wire mode with its tier. |
| EP insertion and schedule | `HeavyFlipControl`, `HeavyFlipRecords`, `ElectricHeavyRecord`, `ChargedInsertion`, `ProtocolToll`, `WireSchedule`, `WireReferenceCost`. The heavy word and candidate light offset use supplied label, address, reference, record, phase and booked costs. | The selector identities and flag and amplitude formulae are fixed for their arguments. An effective insertion, writer input, or chosen reference can only depend on a receiver rule through a certified embedding of that trace and its paid work. |
| EP packet readers | `VacancyProjection`, `ElectricCoordinateDecoder`, `RefreshMap` and the native frame, branch-encoding, register and carrier readers. | The operators act on supplied slots and tags. They have no attachment to the mixed-request receiver. |

EP imports `PMKAutomaton.Interface` and `PMKAutomaton.Values`.
The `Interface.Wire` exports cover the carrier, glued register,
root branch, current and probe used by EP. The
[EP dependency ledger](../PMElementaryParticles/OVERVIEW.md#kautomaton-dependence-of-ep-results)
records the physical inputs to those operations.
`EP.Values.TransportCandidates` (in `PMElementaryParticles.Values`)
indexes the eight checkable witness rows.

Flavor uses the same interface for `LinkFlux`, `ExchangeChirality`,
`MassTermLaw`, `AllRootRestoration`, `RootRepairSelection` and
`HalfTurnAperture`. `ReferenceSafeRestoration` uses the machine root
order comparison. `FlavourPulls` reads the two normalized serial
ratios for its labelled comparison. None of these or the EP modules
imports `LocalController`, `RingReceiver` or `BoundaryErasure`.
The KAutomaton umbrella also exposes those three model modules, so
their observable trace differences matter to a claim of machine symmetry.

## Comparison on the same input

**Derived.** Each expression in `Values` and each EP ledger formula
above is the same function at the same arguments. This includes
the period 43, the short and long serial budgets 60/152 and 36/88,
the normalized rate ratios 1/2 and 3/8, both families of reference
thresholds, and the conditional `α`, `α/2`, `w^q` and
`exp(−T/2)` formulae. The receiver rule is absent from these
definitions. This establishes no equality of supplied physical
clock words, weights, costs or packet traffic.

**Derived.** `LocalController.control_iterates_eq` gives the same
clock, requests and probe from a common start on any trace. The
admitted initial controller support remains a premise. The clock
and comparison theorems in `Interface.Clock` apply to that supplied
support.

**Symmetry, on tagged traces.** `LocalController.tagged_ticks_equal`
gives equality of the complete retained state at every tick.
`tagged_trace_observable_eq` carries that equality through any
common trace readout. `BoundaryErasure.tagged_rule_exports`
identifies the same exported value at every tagged record address.
Supply, restoration, export populations, and any use of the
same paid and disposal maps on that trace agree. The guard
decisions also agree on its diagonal requests
(`guard_decisions_eq_iff`).

## Distinguishing observables

| Status | Quantity that differs | Witness or condition |
| --- | --- | --- |
| Derived | Executed branch | At the same receiver `guard_decisions_eq_iff` makes the decisions differ exactly for a mixed request. This can happen with equal arrivals. |
| Derived | Ordered live and record outputs, live restoration, and destination of the incoming value | `guard_outputs_eq_iff` gives an output difference precisely for mixed requests with unequal arrivals. In `mixed_open_receiver_ports` the retained pair is `(false,true)` for AND and `(true,false)` for OR. If the arriving record is the reference, OR returns it to live and AND leaves it in record. `mixed_open_receiver_destinations` sends the same marked value to the record port at −1 for AND and the live port at +1 for OR. This is different realized transmission, with the constitutive coefficient `α` held fixed. A value's population follows its port. |
| Derived | Receiver comparison flag | `mixed_ring_flags` gives 0 for AND and 1 for OR from the same mixed-request, unequal basis arrivals. This flag is available in the receiver model before any disposition. |
| Conditional | Paid comparison Toll, the associated wire amplitude, and orbit scores in the flag account | If the one mismatch comparison is the charged Toll, `mixed_ring_flag_amplitudes` gives 1 and `exp(−1/2)`. `mixed_ring_orbit_toll` gives site-zero flag rates 0 and 1 on the two orbits from the common input. The [ring flag and survivor tables](RING.md#robustness-across-all-positive-hazards) distinguish the ensembles under stated priors. |
| Excluded | A quotient of all published receiver observations by the rule choice | The same mixed input gives different observable destinations and flags. Equality on tagged starts does not extend to that input. |

## Export-contract requirement

The [propagation table](COMPONENTS.md#what-propagates-downstream)
records why top-down constraints leave the EP reader and return
wiring conditional. Import `PMKAutomaton.Values` for the exact
mixed comparison formula with supplied bookings and work.

`Components.joint_core_iterate` keeps any core-derived observable
independent of the packet-bank operation for the same core start
and rule. `joint_two_fifo_placements_differ` separates actual packet
outputs. `ring_observations_local` bounds both receiver outputs
and the computed flag by the same inputs. This leaves the physical
reader and its tick as inputs. See the
[fan-out cases](COMPONENTS.md#fan-out-at-a-receiver).


**Conditional.** A consumer of the mixed route needs the routed
value and its live or record destination after the visit. The
mixed witness distinguishes the through record at −1 from the
reflected live value at +1. They cannot be represented as the
same boundary record for a reader of that destination. Expose the
equivalent route information if the consumer receives the payload
separately. The destination must stay available through its last use.

**Conditional.** A consumer of a paid receiver comparison needs
to distinguish the visit that executed exchange and its mismatch
flag from bypass. The raw branch can differ even when the arrival
values agree and the mismatch flag is zero. An account of executed
work therefore needs the branch as well as its flag. A reader of
the flag rate or its survival amplitude alone needs the booked
flag account. Disposing of a record is a later operation.

The encoded ring keeps this distinction internally. Its boundary
exports no bit. The tagged open handoff has no rule-dependent
distinction to export. No certified EP trace takes the mixed-route
datum or the mixed receiver's paid comparison as an input. The
stopping point is the use of either datum by an admitted writer
or insertion trace. The affected quantities would be the writer's
input and the Toll, hence amplitude, on that trace.

## Prior and reset checks

**Derived.** `BoundaryErasure.ring_erasure_survivor_eq` gives
the normalized supplied prior on the certified no-export ring.
Every erasure weight is one and there is no extra merger from
boundary erasure. This does not convert a per-orbit prior to a
per-state prior or conversely. Projection onto a smaller set of
retained observables is a separate coarse-graining. On a common
tagged trace, the same projection and erasure map give the same
fibres and weights for both rules at the same starting prior.
The historical ring comparison using receiver flags remains a
different account.

**Conditional.** For the two electric references, let `B` be the
output flag threshold and write `E_C − E_L` for the difference in
booked erased bits per input. With the same paid output flags,
`WireReferenceCost.reference_threshold_with_erasure` gives the
exact threshold `B − (E_C − E_L)` for the remaining difference.
If the two counts agree, the threshold is `B`. The old
`3/4`, `27/32`, `9/10` values require
`E_C − E_L = −B/2` to hold in the replacement account. Their
original proofs use a balanced comparison reset. The certified
tagged train gives no comparison between the two electric writers'
export counts. A numeric erasure-reset threshold is therefore
unfixed, and the existing flag thresholds remain intact.
