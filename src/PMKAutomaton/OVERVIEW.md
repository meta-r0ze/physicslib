# PMKAutomaton — checked results

The results keep their stated hypotheses. Use [TODO](TODO.md) for the open work.
Import `PMKAutomaton.Interface` for transport and `PMKAutomaton.Values` for the checked numbers.

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
