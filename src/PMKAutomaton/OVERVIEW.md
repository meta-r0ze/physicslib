# PMKAutomaton — checked results

The results keep their stated hypotheses. Use [TODO](TODO.md) for the open work.
Import `PMKAutomaton.Interface` for transport and `PMKAutomaton.Values` for the checked numbers.

## Autonomous Boolean ring

`AutonomousRing` tests the requested eight-state alphabet: two native stream bits and
one dynamical local marker. No time-dependent requests or Hamming-code price enter.
This is a restricted machine model, not a selected E8 excitation or vacuum realization.
The old receiver is already autonomous with retained requests as state. Initial data do
not constitute a time-dependent external controller; autonomy alone does not select a rule.

| Constraint | Existing source / exact implementation |
| --- | --- |
| Reversible and number-conserving | `Equiv.Perm`; `Admissible`, `tick_bijective`, `tick_conserves` |
| Empty zero-marker vacuum | `vacuum_fixed`; every empty marked site is fixed too (`empty_fixed`). |
| Reflection with stream exchange | `ClockSymmetry.reversingElement` in Gpm; `clock_line_reflection`, `reflect_tick` |
| Unchanged-marker receiver | OR requests `(marker,false)`; `frozen_receiver_reduction` on ports. |
| Update order | Map then stream uses the incoming-port chart. `incoming_output_conjugacy` relates it to stream then map; phase/probe are not in this alphabet. |
| Local autonomy | `packetStep_uses_local_state`; the marker updates at the packet's site. |
| Exact one-packet restriction | `packetStep_realizes_tick`, `embed_injective`, `packet_iterate_realizes`; valid at every ring size. |

`AutonomousRing.admissible_rules_count` in `AutonomousRingEnumeration`
checks all site permutations by `decide +kernel`: exactly 10 pass.
`explicit_rules_exhaustive` gives the complete table below. Each row has two versions:
at a doubly occupied site the marker either stays or flips. Empty-site markers stay.
`double_flip_unseen` certifies that this choice has no effect on one packet.

| Kind | Marker at a single packet | Stream reversal condition | Rules | Electron hosts at n = 3,5,7,9 |
| --- | --- | --- | --- | --- |
| 0 | Stays | Marker 1 | 2 | 0 |
| 1 | Flips | Never | 2 | 0 |
| 2 | Flips | Marker 1 | 2 | 0 |
| 3 | Flips | Marker 0 | 2 | 0 |
| 4 | Flips | Always | 2 | 0 |

`closed_cycle_even` and `native_closed_cycle_not_one` prove the obstruction for ALL
ring sizes: full-state return restores stream direction, so reversals must be even.
Localization, identity and robustness cannot rescue a one-reversal cycle. The
selected-rule set is empty (`census_domain_empty`), so its census at odd n = 3..13
and n = 43 is empty. Other periodic patterns of the rejected rules are not classified.
Reflection here commutes with evolution; inverse-time conjugacy is a different condition.

## Component contracts

| Part | What to read | Module notes |
| --- | --- | --- |
| Six pillars and port limits | Check the inputs and outputs for each part. | [Components](Components.lean), components, pillars, interactions and classification |
| Joint update and headroom | The packet-bank action is supplied. The lift projects to the core. The margin uses the same units as the load. | [Components](Components.lean) and [Values](Values.lean) |
| Receiver outputs | A visit can deliver a live value, a record or a comparison flag. The consumer must name its input. | [RingReceiver](RingReceiver.lean) and [Interface](Interface.lean) |
| Flags, exports and costs | Compare traces only after the booked events and their units are fixed. | [BoundaryErasure](BoundaryErasure.lean) and [LocalController](LocalController.lean) |

## Admission

| Question | Where to read |
| --- | --- |
| Which start and supply are given? | [OddReferenceSource](OddReferenceSource.lean) and [OpenHandoff](OpenHandoff.lean) |
| What can the clocked trials reach? | [ClockedRootTrials](ClockedRootTrials.lean). The four histories keep both request bits. |
| Which guards are reversible? | [LocalController](LocalController.lean). Compare the tagged trace with the mixed input. |
| What reaches the reader? | [Interface](Interface.lean) and [RingReceiver](RingReceiver.lean). The receiver rule can change a port or a flag. |
| What can the boundary erase? | [BoundaryErasure](BoundaryErasure.lean). The account counts only a supplied export. |

The parked [joint-successor work](TODO.md#reachable-occupied-background) concerns the closed
resource-exchanging execution for decay. It does not define held-event mass. The clean backward reference stream is a supplied
input. Its renewal by the occupied vacuum and its return within one period
are not certified. EP's `ExcitationPersistence` records the exact missing
joint execution and resource account. Zero retained-ring erasures and a
reversible packet lift do not fill this contract.

## Constraints on occupied joint successors

`JointSuccessorConstraints` audits the admissibility contract before a joint
successor is selected. The generic `Components` core has not been identified
with a packet-free physical background. Its one-way projection does imply
packet-independent core trajectories. It does not imply zero gross use of
resources that can be replenished during the same period.

| Question | Checked result or missing definition | Lean entry point |
| --- | --- | --- |
| One-way projection | Equal initial backgrounds have equal background endpoints for all packet banks and horizons. | `packet_independent_background` |
| Resource debit | An identified net loss in a background-only reserve is packet-independent. A zero-bank baseline with zero net loss forces zero net loss for all banks. This is conditional on that account and baseline. | `net_debit_independent`, `zero_baseline_forces_zero_net_debit` |
| Gross consumption | Positive matched consumption and intake can maintain a constant reserve. Capacity alone does not force zero gross consumption. | `positive_matched_flows`, `PMSubstrate.Pillars.capacity_sustains` |
| Conservation and activity | A one-way FIFO preserves packet population, changes an occupied slot and returns the bank in 43 ticks with a fixed background. This algebraic example is not an admitted physical successor. | `one_way_reversible`, `fifo_population_conserved`, `fifo43_nontrivial`, `one_way43_return` |
| Reversibility clause | `Equiv.Perm` supplies the required notion. | `Components.joint_bijective_iff` |
| First missing clause of A | No locality/primitive-root-event predicate classifies arbitrary background × packet-bank permutations. The existing ticks certify their own operations and stencils. | `RecordTransport.tick_local`, `RingReceiver.tick`, `ClockedRootTrials.quiet_trial_tick` |
| Joint charges and labels | Component readouts exist. The total readout on the proposed physical joint state is not identified. | `Components` component contracts |
| Closure clause | Weight invariance is the SCOPE premise. Successor equivariance also needs a joint group action and its justification. G₊ fixes `cu` but need not fix the 43-state reading. | `ClockSymmetry.Gplus`, `swap_changes_clockReading` |
| Empty and clamped cases | An algebraic zero bank exists. A physical no-packet embedding, stationary-family joint encoding and clamping operation remain unspecified. | `Components.PacketBank`, `OddReferenceSource.rest_stationary` |
| Finite reduction | Finite cell/channel indices still give an infinite complex-valued packet state. No faithful finite admissible-successor implementation family is specified. | `packetBank_infinite` |

The requested zero-gross-consumption no-go is not derived. Back-reaction can
be required by a packet-dependent background-resource account, once that
account and its no-packet baseline are identified. It does not follow from
reversibility and period balance alone. The set A is not filled with placeholder
predicates. It is not classified as empty, unique or a family. No selected
successor, loaded-seed derivation or coset-0 contact count follows yet.
The [joint-successor TODO](TODO.md#reachable-occupied-background) names the missing inputs.

## KAutomaton closeout

The conditional joint update, port contract and least-cost rule are in
[Interface](Interface.lean), [Components](Components.lean) and [RingReceiver](RingReceiver.lean).
Admission, clock placement, tariffs and supply stay as named inputs.

<a id="bare-line-stabilizer"></a>

The [bare-line stabilizer](Components.lean) gives the checked E7 generators,
their sector action and the reference for the group orders.

## Native machine

The [machine module](Machine.lean) lists the implementation and its certificates.
The machine builds with PMAction. The packet interface imports it from above.

| Area | Entry modules |
| --- | --- |
| Carriers, parity and vacuum | `CarrierEvents`, `CarrierParity`, `CarrierVacuumSector`, `VectorEvenFrame` |
| Registers, controls and readout | `IndependentRegisters`, `RegisterControl`, `ScheduledReadout`, `InterferenceReadout` |
| Root transfers and reference | `RootTransfer`, `RootTransferPhase`, `RootReferencePreparation`, `NativeReferenceBackground` |
| Records and supply | `RecordTransport`, `RecordSupply`, `OpenReferenceFlow`, `PrimitiveRecordBoundary` |
| Clock and microscopic hop | `ClockRing`, `ClockControlledRoot`, `ClockDynamics`, `AxisHop`, `SliceHop` |
| Native links and locality | `NativePacketUpdate`, `NativePacketRouting`, `NativeCoherentLinks`, `EdgeLocality` |
| Refresh and repair | `RootMaintenance`, `FactorRepair` |
| Finite paths and limits | `FiniteRootWordControls`, `FiniteConfigurationControls`, `NativeConsistency`, `CompactLimits`, `MatterContinuum` |

<a id="node-handoff-and-admittance"></a>
<a id="two-site-handoff-and-the-six-pillars"></a>

## Handoff

| Check | What it gives | Lean names |
| --- | --- | --- |
| Tagged and mixed starts | Tagged starts give the same trace. A mixed start can change a destination and its flag rate. | `LocalController.tagged_trace_observable_eq`, `mixed_open_receiver_destinations`, `RingReceiver.mixed_ring_registration_rate` |
| Local guards | Classify the reversible rows. Two distinct tables give the same tagged open trace. | `LocalController.radius_one`, `receiver_realisation`, `reversible_iff_rows`, `enumerated_rule_count`, `two_open_compatible_rules` |
| Carrier and port routing | Read the native update on the supplied ports. Each site has two live modes and two record modes. | `NativeCarrierProtocol`, `NativePacketRouting`, `NativePacketUpdate`, `TwoSiteHandoff.port_count` |
| Exchange and bypass | Trace the live and record destinations. A supplied root half-pulse realizes exchange. | `TwoSiteHandoff.step_trace`, `export_trace`, `receiver_half_pulse`, `OpenReferenceFlow.exchange_reflects`, `bypass_transmits` |
| Closed pair | Four exchanges return the full state. Four restorations need the reference in all four slots. | `TwoSiteHandoff.first_reference_iff`, `second_reference_iff`, `exchange_four_returns`, `four_restorations_iff` |
| Through weight | The current law gives the through weight. Product weights need independent steps with equal weights. | `HandoffAdmittance.node_current`, `through_eq_conductance`, `direct_crossing_prob`, `Interface.Handoff.through_weight_eq_alpha` |
| Pulse calibration | Read the principal exchange area on a through pulse. The clock duration and wall-rate conversion remain inputs. | `Interface.Handoff.principal_through_area_eq`, `HandoffAdmittance.two_pass_alternative`, `reflected_event_ne_alpha`, `pulse_calibration_transfers` |

<a id="open-route-and-reference-supply"></a>
<a id="odd-rest-modes-as-occupied-reference-candidates"></a>

## Record

| Check | What it gives | Lean names |
| --- | --- | --- |
| Coherent recording | Unequal outputs with overlap need orthogonal records. A supplied reversible reset stores the displaced state. | `CoherentGate.unequal_needs_orthogonal`, `CoherentRecordRestoration.prepared_repair`, `unitary_reset_factorization`, `twice_undoes` |
| Open line | Trace arrivals and exports for each supplied visit. A three-site start fixes only the first visit. | `OpenHandoff.address_step`, `receiver_trace`, `export_trace`, `any_incoming_trace`, `neighbours_do_not_determine_second_visit` |
| Readiness | Check the supplied population and accepted error. Distinguish an open orbit from a finite ring return. | `OpenHandoff.acceptance_iff_supply`, `population_required`, `basis_loading_iff`, `RecordSupply.open_orbit_forever`, `ring_returns` |
| Odd reference | The sharp seed fails the odd-sector test. A supplied occupied rest mode can load the ready port. | `OddReferenceSource.basis_label_not_odd`, `root_phase_word_no_basis`, `rest_stationary`, `rest_population`, `first_wall_ports`, `odd_seed_train_restores` |

## Cost

| Check | What it gives | Lean names |
| --- | --- | --- |
| Request complement | One visit has a complement identity. A clocked trace need not have this symmetry. | `LocalController.complemented_output`, `receiver_dual_not_conjugate`, `receiver_dual_flag_counterexample` |
| Erasure | A booked binary reset counts one bit. The retained ring exports zero bits. | `BoundaryErasure.erasing_pays_one`, `erasedBitsPerTick`, `ring_cycle_erasure`, `tagged_rule_exports` |
| Closed-ring selection | Enumerate the finite orbits. Both rules attain the least registration rate on the certified family. | `RingReceiver.orbit_enumeration_covers`, `orbitRegistrationRate`, `minimum_orbit_registration_rate`, `both_rules_attain_best_survival` |
| Weighted visits | Sum the flags with the supplied visit weights. Uniform ports give zero exchange flag cost. | `LocalController.traceExchangeFlagCost`, `uniform_trace_exchange_flag_cost`, `uniform_remaining_cost_iff` |
| Booked events | Group registrations by owner. Add the bits erased at the boundary. | `NetCost.expected_count_linear`, `Components.booked_registration_and_erasure_sum` |
| Root attempts | Multiply the Bernoulli attempt law by the uniform carrier law. The expected cost includes the active carrier fraction. | `RootTransferAccounting.rootAttemptPMF`, `root_attempt_pmf_normalized`, `expected_root_cost` |
| Selection and refresh | Compare the supplied families and prices. A least-cost refresh uses the required job ledger. | `PersistenceSelection.within_family_iff_cheapest`, `RefreshSchedule.minimal_is_ledger`, `CoherentRefresh.minimum_once` |
| Reference comparisons | Read the conditional output and balanced-reset thresholds. | `Values.outputFlagThreshold_eq`, `balancedResetThreshold_eq`, `WireReferenceCost.balanced_reset_gap_eq_values` |

<a id="calibrating-the-root-clock"></a>

## Clock

The period is `PMSubstrate.E8Values.Delta`. The [machine clock geometry](Machine/ClockRing.lean)
uses the substrate lattice pairing. The [clock values](Values.lean) keep the word lengths and
rate ratios. The [interface notes](Interface.lean) give the supplied clock placements.

| Check | What it gives | Lean names |
| --- | --- | --- |
| Period | One full clock has 43 phases. A closed mask excursion can fire in two phases. | `E8Values.Delta_eq`, `ClockControlledRoot.cycle_closes`, `CarrierReferenceCycle.excursion_boundaries` |
| Serial words | The root half-pulse takes two quarter-times. Word bounds use the stated serial schedule. | `RootTransferPhase.half_pulse_word`, `Values.shortSerialTicks`, `longSerialTicks` |
| Alias and calibration | Integer samples can identify several gaps. A trial statistic or a principal-range witness fixes the calibrated gap. | `RootClockCalibration.phase_alias_iff`, `trial_weight_inj`, `gap_from_trials`, `principal_flag_inj` |
| Two retained trials | The request pair fixes the endpoint. The four histories do not supply their own physical prior. | `ClockedRootTrials.pair_endpoint`, `historyCount`, `all_pairs_history_count`, `shared_request_history_count`, `history_pmf_factorizes` |
| Common clock | A supplied relation between a statistical pair and two ticks sets the generator per tick. A common tick cancels from the rate ratio. | `ClockedRootTrials.phase_in_ticks`, `CertainTransferRate.common_tick_rate_ratio`, `Values.equal_normalization_rate` |
| Clock-plane projection | Read each coset's drift per lap. The vector class has transverse-silent closure. | `ClockPlaneProjection.cospinor_lap`, `spinor_lap`, `vector_self_closing`, `self_closing_iff` |

<a id="heavy-label-application"></a>

## Full clock-root symmetries

The clock root is `ClockPlane.cu`. The full 43-state reading also uses `cv`.
Do not apply a root-stabilizer invariance statement to that reading without
checking the second clock vector.

| Object | Definition or result | Lean entry point |
| --- | --- | --- |
| Ambient group | All products of E8 root reflections act as integral lattice isometries. | `ClockSymmetry.Weyl`, `rootReflection`, `weyl_norm` |
| Full G₊ | Keep both aligned D4 factors and fix `cu`. Sector preservation is commutation with twice the orthogonal projector. | `Gplus`, `projector_sectors`, `maps_spacetime`, `maps_internal` |
| Full G± | Keep both factors and fix `cu` up to sign. | `Gpm` |
| Quotient | D4 plus D4 has index four. Both factor discriminants receive the same permutation. | `sector_annihilator`, `keyAction_descent`, `diagonal_glue` |
| Glue image | Both full groups induce exactly identity and the spinor-key swap. The clock key (0,1) is fixed. | `full_generation_image` |
| Generators | Six D3 reflections and a two-root glued word generate G₊. An eight-root negation word extends it to G±. | `ClockSymmetryGenerators`, `positive_generators_exhaustive`, `line_generators_exhaustive` |
| Normal form | Each factor permutes and signs its three transverse axes. The two outer signs agree. | `ClockSymmetryNormalForm`, `ClockSymmetryFrames`; `spatial_frames`, `integral_sign_parity` |
| Orientation | The same nontrivial glue swap has spatial determinants -1 and +1. | `swap_orientations` |
| Clock limit | The displayed swap does not preserve the reading that uses `cv`. | `swap_changes_clockReading` |

The [EP generation table](../PMElementaryParticles/OVERVIEW.md#generation-orbits)
adds the existing generation-specific channel placement. This is a separate
restriction from the bare clock root and the two factors.

## Route

| Check | What it gives | Lean names |
| --- | --- | --- |
| Wall pairs | The omitted class labels the packet. A crossing word acts on the two walls. | `GenerationWalls.one_class_per_wall`, `GenerationEncoding.carriers_per_packet_card`, `GluedRegister.crossing_word_glued` |
| Stationary reference | The stated node model gives the direct and two-leg routes. A stationary reference and the route admission remain inputs. | `ReferenceClassHop.stationary_iff`, `ReferenceNode.restoring_two_classes`, `direct_three_classes`, `restoring_series` |
| Heavy label | A supplied companion seed permits a guarded crossing. The setup has conditional flag sums on the active and static sides. | `ElectricCompanionBank.guarded_companion_transport`, `ElectricCompanionSetupFlagCosts.primitive_setup_sum` |

### Implementation imports

| Reader | Implementation it uses |
| --- | --- |
| `ControlledGluedRegister`, `DoubletSign` | `GluedRegister` and `CarrierWeyl` |
| `RefreshMap`, `HeavyFlipNativeBoundary` | `ClockControlledRoot` and `InBandRootReadout` |
| `ElectricCompanionBank`, `ElectricChiralKick`, `ElectricHeavyRecord` | `CarrierTriality`, `RegisterInteraction` and `RootBranchEncoding` |
| `ReferenceSafeRestoration` | `RootOrderComparison` |

## Reversibility boundary

Keep the records in the reversible state until their last use.
The comparison flag is an observation. A booking determines whether it is paid.
A separate export can be kept, returned or erased. The retained update and the
boundary operation have different hypotheses. See [BoundaryErasure](BoundaryErasure.lean).

The packet interface follows PMConstants. The machine modules build with PMAction.
The [dependency audit](../AuditDependencies.lean) checks these boundaries.
