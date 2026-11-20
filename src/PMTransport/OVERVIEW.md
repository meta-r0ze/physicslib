# PMTransport — checked results

Import `PMTransport.Interface` for the theorem families below and
`PMTransport.Values` for the numbers. Results retain their theorem
hypotheses. Physical inputs are in the [premise ledger](PREMISES.md).
The [component inventory](COMPONENTS.md) maps the six pillars, native ports
and open connections. `PMTransport.Components` exposes the corresponding
contracts with explicit hypotheses. The [machine overview](Machine/OVERVIEW.md)
maps the upstream implementation.
The [Transport closeout](COMPONENTS.md#transport-closeout) links
the marked Weyl stabilizers, the equivariance and conservation
filters, and conditional least Toll. The public symmetry exports
identify the embedded carrier reflections.
The inventory gives the [encoded rate limits](COMPONENTS.md#per-instance-rates),
[headroom](COMPONENTS.md#margin-in-matching-units),
[reversible packet-bank lift](COMPONENTS.md#joint-update-and-its-limit),
and [booked Toll account](COMPONENTS.md#toll-by-operation).
The [admission check](ADMISSION.md) gives the reachable trial histories
and the boundary required for repeated open visits. Its
[autonomous guard test](ADMISSION.md#no-external-controller) checks
the effect of retaining all controls in the state.

<a id="node-handoff-and-admittance"></a>
<a id="two-site-handoff-and-the-six-pillars"></a>

## Handoff

| Result | Certificates and scope |
| --- | --- |
| Tagged equivalence and mixed-request readouts | `LocalController.tagged_trace_observable_eq` gives equality on tagged starts. `mixed_open_receiver_destinations` and `RingReceiver.mixed_ring_orbit_toll` distinguish the mixed outputs and flag rates. The [downstream audit](DOWNSTREAM.md) identifies the records a downstream read would need. |
| Reversible local guards | `LocalController.radius_one`, `receiver_realisation`, `reversible_iff_rows` and `enumerated_rule_count` classify the guarded two-stream encoding. `tagged_open_iterate` and `two_open_compatible_rules` give distinct rules realizing the same tagged open trace. |
| Carrier and port routing | `NativeCarrierProtocol`, `NativePacketRouting`, `NativePacketUpdate` give native readout and locality for the supplied routing. `TwoSiteHandoff.port_count` gives two live and two record modes per site. See the [substrate pillars](../PMSubstrate/Pillars.lean) and [wire application](../PMElementaryParticles/README.md#the-six-pillars-on-the-wire). |
| Exchange and bypass | `TwoSiteHandoff.arrivals_observed`, `step_trace`, `export_trace`, `exchange_lookup`, `native_step_observed`, `receiver_agrees_with_line` give the destinations. `receiver_half_pulse` realizes exchange on an admitted root phase. `OpenReferenceFlow.exchange_reflects`, `bypass_transmits` identify the reflected and through streams. |
| Closed pair | `TwoSiteHandoff.first_reference_iff` and `second_reference_iff` identify the source of each restoring reference. `exchange_four_returns` returns the full state. `four_restorations_iff` requires all four initial slots to hold the reference. |
| Through weight and direct path | `HandoffAdmittance.node_current`, `through_eq_conductance`, `handoff_from_conductance`, `direct_crossing`, `direct_crossing_prob`. `Interface.Handoff.through_weight_eq_alpha` specializes the current identity to a pulse with through weight `cos² t`. Products require independent steps with the same weight. `HandoffAdmittance.closure_one_price` compares indistinguishable crossings. |
| Calibration limits | `HandoffAdmittance.two_pass_alternative` distinguishes the two-pass mixture. `reflected_event_ne_alpha` excludes a uniform single-reflection flag. `one_tick_cost_endpoint` minimizes with fixed branch costs. `pulse_calibration_transfers` uses the same preparation and detector for both labels. |

<a id="open-route-and-reference-supply"></a>
<a id="odd-rest-modes-as-occupied-reference-candidates"></a>

## Record

| Result | Certificates and scope |
| --- | --- |
| Coherent recording and restoration | `CoherentGate.unequal_needs_orthogonal` requires orthogonal records for unequal outputs with overlap. `CoherentRecordRestoration.prepared_repair`, `unitary_reset_factorization`, `twice_undoes` identify the displaced state and constrain reuse. `IndependentRegisters` and `RegisterControl` provide reversible controls. |
| Open line and export | `OpenHandoff.address_injective`, `address_is_site`, `address_step` realize the primitive D₄ line. `receiver_trace`, `export_trace` identify the arrivals and distinct displaced-record destinations. `any_incoming_trace` restores a common reference for any supplied live sequence. `sum_exported` preserves the displaced population. `neighbours_do_not_determine_second_visit` identifies the three-site horizon limit. |
| Ready reference and renewal | `OpenHandoff.acceptance_iff_supply`, `population_required`, `basis_population_required`, `basis_loading_iff` govern acceptance, population and exact loading. `RecordSupply.open_orbit_forever`, `lattice_forever`, `ring_returns` distinguish open renewal from finite returns. `ReferenceMaintenance` and `HomogeneousRouting` support the supplied orbit. |
| Odd reference | `OddReferenceSource.basis_label_not_odd`, `root_phase_word_no_basis` exclude the sharp `RootReferencePreparation` seed from odd input under the checked phases. `ReferenceSourceBoundary` gives the uniform-source limits. `rest_stationary`, `rest_population`, `wall_loader_unitary`, `load_rest_mode`, `rest_modes_distinct`, `loading_pulse_stays_at_rest`, `first_wall_ports`, `odd_seed_train_restores` give an alternative from a supplied occupied rest state. |

## Cost

| Result | Certificates and scope |
| --- | --- |
| Request complement and receiver swap | `LocalController.complemented_output` gives a one-visit identity. `receiver_dual_not_conjugate`, `no_request_complement_conjugacy` give the clocked obstruction. `receiver_dual_population` preserves the summed port population and `receiver_dual_flag_counterexample` distinguishes the flags. |
| Erasure at a separate export port | `BoundaryErasure.identity_bijective` preserves the protected update. `erasing_pays_one` counts a booked binary erasure. `ring_cycle_erasure` gives zero on the retained ring. `tagged_rule_exports` gives the common open export train. See the [reversibility audit](REVERSIBILITY-AUDIT.md). |
| Closed-ring selection | `RingReceiver.tick_bijective` and `orbit_enumeration_covers` give the finite traffic model. `minimum_orbit_toll` and `both_rules_attain_best_survival` give the tied minima. `survivor_mass_of_subset` gives rule shares for a supplied prior. The [ring ledger](RING.md#robustness-across-all-positive-hazards) gives the exact hazard sign profiles. |
| Guard selection on uniform ports | `LocalController.exchange_flag_realisation` and `uniform_trace_exchange_toll` give the exchange account. `uniform_flag_persistence_tie` and `uniform_remaining_cost_iff` distinguish the certified tie and its missing tariff. |
| Flags and registrations | `TwoSiteHandoff.hop_flag`, `exchange_flag` and `OpenHandoff.receiver_flag` give comparison flags. `DiagonalReadout.state_flag` gives the diagonal mixed-population formula. `NetCost.expected_count_linear` sums expected flags under the supplied sampling law. |
| Pulse and reset accounts | `BranchPulseContract.comparison_mem` and `program_correct` certify the comparisons under the supplied control. `OpenHandoff.balanced_basis_repair_flag` prices a paid exact comparison of a balanced bit with fresh zero. |
| Survival and selection | `TollAmplitude.wireAmplitude_eq` gives `exp(−T/2)`. `PersistenceSelection.within_family_iff_cheapest` compares the supplied family and costs. `RefreshSchedule.minimal_is_ledger` and `CoherentRefresh.minimum_once` characterize minimum refresh at supplied prices. |
| Conditional reference thresholds | `Values.outputFlagThreshold_eq`, `balancedResetThreshold_eq` give the output-only and separately paid balanced-reset thresholds. `WireReferenceCost.packet_record_difference_eq_values`, `balanced_reset_gap_eq_values` connect them to the [packet account](../PMElementaryParticles/SCHEDULE.md#record-reference-remains-undetermined). |

<a id="calibrating-the-root-clock"></a>

## Clock

| Result | Certificates and scope |
| --- | --- |
| Period and words | `E8Values.Delta_eq`, `ClockPeriod`, `ClockDynamics`, `ClockControlledRoot` give the period and reversible clocked words. `RootTransferPhase.quarterTime`, `half_pulse_word` give the root time and serial crossing. See the [clock ledger](CLOCK.md#certified-clock-results) for the short and long bounds and `Values` for their direct and restoring counts. |
| Gap aliases and calibration | `RootClockCalibration.phase_alias_iff`, `integer_samples_agree`, `ambiguous_exchange_clock` give the whole-tick alias. `trial_weight`, `gap_from_trials`, `trial_weight_inj`, `odd_seed_trial_weight` give the statistical calibration. `exchange_tick_iff`, `principal_trial_weight`, `principal_flag_inj` give the principal-range calibration. |
| Two retained trials | `ClockedRootTrials.pair_endpoint`, `shared_fire`, `matches_independent_trial_weight` give the endpoint law. `heat_after_two_ticks`, `phase_in_ticks`, `exchange_in_ticks_iff`, `principal_weight_in_ticks` give the conversion if a statistical pair occupies two coherent ticks. `iterate_controls`, `quiet_trial_tick`, `trial_period_endpoint` give the isolated trace over one period. `history_count_pos_iff`, `all_pairs_history_count` and `shared_request_history_count` give the conditional counts. |
| Conditional rate ratios | `CertainTransferRate.common_tick_rate_ratio` and `Values.equal_normalization_rate` give the [rate comparison](CLOCK.md#flip-to-crossing-rate) with the stated areas, conversion factors and clock. |

<a id="heavy-label-application"></a>

## Route

| Result | Certificates and scope |
| --- | --- |
| Wall pairs and crossings | `GenerationWalls.one_class_per_wall` and `GenerationOrientation.type_label` identify the glue address for a frozen orientation. `GluedRegister.crossing_word_glued`, `crossing_word_pure` and `CarrierTriality` give crossings and the `M/2` relabeling of odd amplitudes on a diagonal glued carrier. |
| Stationary reference and node route | `ReferenceClassHop.stationary_iff`, `touches_reference_class` test direct exchange against a chosen stationary reference. `ReferenceNode.restoring_two_classes`, `direct_three_classes`, `restoring_series` give the two route types and the two-equal-leg result in the stipulated model. |
| Heavy-label candidate | The [companion-bank results](../PMElementaryParticles/OVERVIEW.md#triality-preparation-on-the-companion) give the setup with a supplied seed. `ElectricCompanionSetupToll.primitive_setup_sum` gives the conditional active and static setup flag sums of `1/2` and `3/4`. |

### Implementation imports

`ControlledGluedRegister` still uses raw `GluedRegister` frames and reflections.
`DoubletSign` and `RefreshMap` use `CarrierWeyl` operators.
`RefreshMap` uses `ClockControlledRoot` for the actual scheduled update.
`RefreshMap` and `HeavyFlipNativeBoundary` use `InBandRootReadout` for the root decoder.
`ElectricCompanionBank` uses `CarrierTriality` to prepare its bank.
`ElectricChiralKick` uses `RegisterInteraction` for its current.
`ElectricHeavyRecord` uses `RootBranchEncoding` for the branch decoder.
`ReferenceSafeRestoration` uses `RootOrderComparison` for its order test.
These constructions use implementation definitions outside the interface.

The packet-level interface follows PMConstants. PMAction and PMConstants
can still import the upstream machine modules. The
[dependency audit](../AuditDependencies.lean) checks the layer boundaries.
